-- Prove2me | Theorems.Thm_DriverSurge_IC_lemma_6
-- name    : DriverSurge.IC.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:12.747964+00:00
-- url     : https://prove2.me/theorems/dd945996-5769-4781-86d7-15ddc51629c2
-- title:
--   Lemma 6, p. 57 — ∂/∂u R(w, σ) = λ_if_i(u)·uQ_jT_iT_j/(Q_iT_j + Q_jT_i)²·r(u, i, w, σ), so ∂/∂u R ∝ r
-- statement:
--   Let the trip-length laws have bounded densities $f_1,f_2$, let $\sigma$ be a policy, and let $w_k$ and $\tau$ be $F_k$-integrable on $\sigma_k$ ($k=1,2$). Fix a state $i$ and a point $u>0$ at which $f_i$ and $w_i$ are continuous. Then the marginal gain of the closed-form reward $R(w,\sigma)$ from adding $u$ to $\sigma_i$ exists and equals
--   $$\frac{\partial}{\partial u}R(w,\sigma)=\lambda_i f_i(u)\,\frac{u\,Q_jT_iT_j}{(Q_iT_j+Q_jT_i)^2}\;r(u,i,w,\sigma),$$
--   $$r(u,i,w,\sigma)=\frac{q_{i\to j}(u)}{u}\Delta_{ji}+\frac{w_i(u)}{u}\Big(\frac{Q_i}{T_i}+\frac{Q_j}{T_j}\Big)-\Big(\frac{Q_i}{T_i}R_j+\frac{Q_j}{T_j}R_i\Big),$$
--   where $\Delta_{ji}=R_j-R_i$ and $Q_k$, $T_k$, $R_k$ are evaluated at $\sigma_k$. In particular $\partial R/\partial u$ has the sign of $r(u,i,w,\sigma)$ wherever $f_i(u)>0$, which is the paper's $\partial R/\partial u\propto r$.
--
--   The function $r$ drives the structural analysis: its monotonicity or quasi-convexity in $u$ determines the shape of the optimal policy (Lemma 5, Theorem 4).
--
--   **Formalization Note** Lean state `0` is the paper's non-surge state 1 and Lean state `1` the surge state 2; `other i` is the state $j\ne i$. The marginal gain is the limit of $\big(R(\sigma_i\cup(u,u+h))-R(\sigma_i\setminus[u,u+h])\big)/h$ as $h\downarrow0$, with the other state's policy fixed.
--
--   Differences from the source:
--   - generalization: $\partial R/\partial u\propto r$ (same sign except where $f_i(u)=0$) → the exact value $\lambda_if_i(u)uQ_jT_iT_j(Q_iT_j+Q_jT_i)^{-2}\,r$; reason: the factor is positive where $f_i(u)>0$, so the exact formula implies the sign statement; it is the paper's own computation on p. 62
--   - reading: $\partial/\partial u\int_{\sigma_i}g\,dF_i=g(u)f_i(u)$ under bounded densities → $f_i$ and $w_i$ continuous at $u$; reason: the pointwise value $f_i(u)$ of a density is meaningful only at continuity points; the paper's computation uses it there
--   - reading: the derivative with respect to an upper endpoint $u$ of $\sigma_i$ → the marginal gain from adding $(u,u+h)$, at every $u>0$; reason: "the infinitesimal gain in the value of $\hat R(\sigma)$ by adding $u$ to the set $\sigma$" (p. 50); at an upper endpoint it is the derivative in the endpoint
--   - encoding: the formulas use $\int_{\sigma_k}\tau\,dF_k$ and $\int_{\sigma_k}w_k\,dF_k$ without saying they are finite → $\tau$ and $w_k$ are assumed $F_k$-integrable on $\sigma_k$; reason: the quantities $T_k$, $W_k$, $R_k$ are undefined otherwise (Lean's integral would be the junk value 0); only undefined cases are excluded
--   - generalization: D.3.1's standing assumption (p. 56) that state 2 dominates state 1 ($\exists\sigma_2$ with $\Delta(\sigma_2,\sigma_1)>0$ for all $\sigma_1$) → not assumed; reason: the derivative computation does not involve it; the formula holds for every $w$, so it specializes to the source under the assumption
-- source:
--   Garg, Nazerzadeh, Driver Surge Pricing, arXiv:1905.07544v4, p. 57, Lemma 6 (proof p. 62)

import Mathlib
import Definitions.Def_DriverSurge_IC_Pricing

namespace DriverSurge.IC

open MeasureTheory Set

/-- Lemma 6 (pp. 57, 62), exact form. Let `σ` be a policy with `w_k` and `τ` integrable on `σ_k`
(`k = 1, 2`), let `F_i` have a bounded density `f_i`, and let `u > 0` be a point where `f_i` and `w_i` are
continuous. Then the marginal gain of `R(w, σ)` from adding `u` to `σ_i` is
`λ_i f_i(u) · u Q_j T_i T_j / (Q_iT_j + Q_jT_i)² · r(u, i, w, σ)`,
so `∂/∂u R(w, σ)` has the sign of `r(u, i, w, σ)` wherever `f_i(u) > 0`. -/
theorem lemma_6 (P : Primitives) (f : Fin 2 → ℝ → ℝ) (hf : HasBoundedDensity P f)
    (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ) (hσ : IsPolicy σ)
    (hw : ∀ k, IntegrableOn (w k) (σ k) (P.F k))
    (hτ : ∀ k, IntegrableOn (fun τ : ℝ => τ) (σ k) (P.F k))
    (i : Fin 2) (u : ℝ) (hu : 0 < u) (hfu : ContinuousAt (f i) u) (hwu : ContinuousAt (w i) u) :
    HasMarginalGain (rewardOn P w σ i) (σ i) u
      (P.lam i * f i u * u * Qn P (other i) (σ (other i)) * Tn P i (σ i) * Tn P (other i) (σ (other i)) /
          (Qn P i (σ i) * Tn P (other i) (σ (other i)) + Qn P (other i) (σ (other i)) * Tn P i (σ i)) ^ 2 *
        rFun P w σ i u) := by sorry

end DriverSurge.IC
