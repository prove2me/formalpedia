-- Prove2me | Theorems.Thm_DriverSurge_IC_remark_1_continuity
-- name    : DriverSurge.IC.remark_1_continuity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:07.893639+00:00
-- url     : https://prove2.me/theorems/c6eccb33-8087-4826-96cb-b9cb47438480
-- title:
--   Remark 1, bullets 1–2, p. 57 (corrected: ∂R/∂u continuous in u for continuous densities) — R_i, R, µ_i, r and ∂/∂u R are continuous in σ and u
-- statement:
--   Let the trip-length laws have bounded densities and finite means, and let the payments $w_1,w_2$ be continuous on $(0,\infty)$ and $F_k$-integrable there. Measure the distance between policies $\sigma,\sigma'$ by $F_1(\sigma_1\triangle\sigma_1')+F_2(\sigma_2\triangle\sigma_2')$. Then, for each state $i$:
--
--   1. $R_i(w_i,\sigma_i)$, $R(w,\sigma)$ and $\mu_i(\sigma)$ are continuous in $\sigma$;
--   2. $r(u,i,w,\sigma)$ is continuous in $u\in(0,\infty)$ for fixed $\sigma$, and continuous in $\sigma$ for fixed $u>0$;
--   3. the marginal gain
--   $$D(\sigma,u)=\frac{\partial}{\partial u}R(w,\sigma)$$
--   (with respect to state $i$'s policy) is continuous in $\sigma$ for fixed $u>0$, and, if moreover the densities $f_1,f_2$ are continuous on $(0,\infty)$, continuous in $u\in(0,\infty)$ for fixed $\sigma$.
--
--   These continuity properties are hypotheses 1–3 of Lemma 5, which turns the sign analysis of $r$ into the shape of the optimal policy.
--
--   **Formalization Note** Lean state `0` is the paper's non-surge state 1 and Lean state `1` the surge state 2; `other i` is the state $j\ne i$. Item 3 is stated for every function $D$ that is the marginal gain of the reward at every policy and every $u>0$.
--
--   Differences from the source:
--   - correction: $\partial/\partial u R(w,\sigma)$ continuous in $u$ under bounded densities → continuity in $u$ claimed when the densities are continuous on $(0,\infty)$; continuity in $\sigma$ claimed unconditionally; reason: by Lemma 6 the derivative is $\lambda_if_i(u)\cdot(\text{positive})\cdot r(u)$, so it jumps in $u$ where $f_i$ jumps and $r\ne0$: with all rates $1$, $F_1=F_2$ uniform on $(0,1)$, $w_1(u)=u$, $w_2(u)=2u$ (state 2 dominates: $R_2(w_2,(0,1))=2/3>1/3\ge R_1$) and $\sigma=$ accept-all, the marginal gain is $0$ at $u=1$ (no mass to the right) but tends to $\lambda_i\cdot(\text{positive})\cdot r(1)\ne0$ as $u\uparrow1$ ($r(1,1,w,\sigma)=1$, $r(1,2,w,\sigma)\approx2.42$)
--   - reading: "continuous in $\sigma$" → continuity with respect to $F_1(\sigma_1\triangle\sigma_1')+F_2(\sigma_2\triangle\sigma_2')$; reason: the metric used in the proof of Lemma 5 (p. 52: $F(\sigma'\setminus\sigma'_\delta\cup\sigma'_\delta\setminus\sigma')<\delta$)
--   - encoding: "given assumptions on $F_i$, $w_i$" → bounded densities, finite means, $w_k$ continuous on $(0,\infty)$ and $F_k$-integrable; reason: D.3.1's standing assumption and p. 5's continuity; finite means and integrability exclude the cases where $T_i$, $W_i$ are undefined
--   - generalization: $w_k$ asymptotically sub-linear (p. 5) → not assumed; reason: the remark does not use it; integrability already makes the rates finite
--   - generalization: D.3.1's standing assumption (p. 56) that state 2 dominates state 1 ($\exists\sigma_2$ with $\Delta(\sigma_2,\sigma_1)>0$ for all $\sigma_1$) → not assumed; reason: the continuity properties do not involve it; they hold for every $w$, so they specialize to the source under the assumption
-- source:
--   Garg, Nazerzadeh, Driver Surge Pricing, arXiv:1905.07544v4, p. 57, Remark 1 (bullets 1–2)

import Mathlib
import Definitions.Def_DriverSurge_IC_Pricing

namespace DriverSurge.IC

open MeasureTheory Set

/-- Remark 1, bullets 1–2 (p. 57; corrected: the continuity of `∂/∂u R(w, σ)` in `u` is claimed when
the densities are continuous on `(0, ∞)`). Let `F_i` have bounded densities and finite means, and let
the payments `w_i` be continuous on `(0, ∞)` and `F_i`-integrable there. Continuity in `σ` is with
respect to `F_1(σ_1 △ σ'_1) + F_2(σ_2 △ σ'_2)` over policies.
1. `R_i(σ)`, `R(σ)` and `µ_i(σ)` are continuous in `σ`;
2. `r(u, i, w, σ)` is continuous in `u > 0` for fixed `σ` and continuous in `σ` for fixed `u`;
3. every marginal gain `∂/∂u R(w, σ)` (with respect to state `i`'s policy) is continuous in `σ` for
   fixed `u > 0`, and, if the densities are continuous on `(0, ∞)`, continuous in `u > 0` for fixed
   `σ`. -/
theorem remark_1_continuity (P : Primitives) (f : Fin 2 → ℝ → ℝ) (hf : HasBoundedDensity P f)
    (hmean : FiniteMean P) (w : Fin 2 → ℝ → ℝ) (hwc : ∀ k, ContinuousOn (w k) (Ioi 0))
    (hwi : ∀ k, IntegrableOn (w k) (Ioi 0) (P.F k)) (i : Fin 2) :
    ContinuousInPolicy P (fun σ => stateRate P i (w i) (σ i)) ∧
    ContinuousInPolicy P (fun σ => rewardCF P w σ) ∧
    ContinuousInPolicy P (fun σ => mu P σ i) ∧
    (∀ σ, IsPolicy σ → ContinuousOn (rFun P w σ i) (Ioi 0)) ∧
    (∀ u : ℝ, 0 < u → ContinuousInPolicy P (fun σ => rFun P w σ i u)) ∧
    (∀ D : (Fin 2 → Set ℝ) → ℝ → ℝ,
      (∀ σ, IsPolicy σ → ∀ u : ℝ, 0 < u → HasMarginalGain (rewardOn P w σ i) (σ i) u (D σ u)) →
      (∀ u : ℝ, 0 < u → ContinuousInPolicy P (fun σ => D σ u)) ∧
      ((∀ k, ContinuousOn (f k) (Ioi 0)) → ∀ σ, IsPolicy σ → ContinuousOn (D σ) (Ioi 0))) := by sorry

end DriverSurge.IC
