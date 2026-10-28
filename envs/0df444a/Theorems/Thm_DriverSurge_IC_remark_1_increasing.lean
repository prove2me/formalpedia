-- Prove2me | Theorems.Thm_DriverSurge_IC_remark_1_increasing
-- name    : DriverSurge.IC.remark_1_increasing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:17.169063+00:00
-- url     : https://prove2.me/theorems/5ed59ce3-624d-4cbd-8b89-a5c507ec3e8e
-- title:
--   Remark 1, bullet 4, p. 57 (corrected: U ∈ [0, ∞]) — if ∆_{ji} < 0 and w_i(u)/u non-decreasing, r(u, i, w, σ) is strictly increasing, negative below U and positive above
-- statement:
--   Let $\sigma$ be a policy with $w_k$ and $\tau$ $F_k$-integrable on $\sigma_k$. Fix a state $i$ with other state $j$, and suppose
--   $$\Delta_{ji}=R_j(w_j,\sigma_j)-R_i(w_i,\sigma_i)<0\quad\text{and}\quad u\mapsto w_i(u)/u\ \text{is non-decreasing on }(0,\infty).$$
--   Then $r(u,i,w,\sigma)$ is strictly increasing in $u\in(0,\infty)$, and there is $U\in[0,\infty]$ such that $r(u,i,w,\sigma)<0$ for $0<u<U$ and $r(u,i,w,\sigma)>0$ for $u>U$. By Lemma 6, $\partial R(w,\sigma)/\partial u$ has the same sign wherever $f_i(u)>0$.
--
--   This is the surge-state case: it says the surge-state policy rejects short trips, the form $(t,\infty)$.
--
--   **Formalization Note** Lean state `0` is the paper's non-surge state 1 and Lean state `1` the surge state 2; `other i` is the state $j\ne i$.
--
--   Differences from the source:
--   - correction: a sign change at $U\in(0,\infty)\cup\{\infty\}$ → $U\in[0,\infty]$; reason: $U=0$ occurs, also under D.3.1's standing assumptions: with all rates $1$, $F_1=F_2$ uniform on $(0,1)$, $i=2$, $w_2(u)=u$, $w_1\equiv0$ (so state 2 dominates state 1), $\sigma_2=(0,\infty)$ and $\sigma_1=\emptyset$, one has $\Delta_{ji}=-1/3<0$ and $r(u,i,w,\sigma)\ge\big(Q_i-\lambda_{i\to j}(T_i-1)+\lambda_{j\to i}\big)/T_i>0$ for all $u>0$ (here $T_i=3/2$), so $r$ is never negative
--   - reading: "Thus, $\partial R/\partial u$ is negative up to … and positive thereafter" → the sign change stated for $r$; reason: D.3.1 defines $\propto$ as "same sign except where $f(u)=0$", so the claim about $\partial R/\partial u$ is the claim about $r$ (Lemma 6)
--   - reading: "(i = 2 the surge state)" → stated for each state $i$; reason: the parenthesis labels the typical case; the hypotheses are $\Delta_{ji}<0$ and monotonicity of $w_i(u)/u$
--   - encoding: the formulas use $\int_{\sigma_k}\tau\,dF_k$ and $\int_{\sigma_k}w_k\,dF_k$ without saying they are finite → $\tau$ and $w_k$ are assumed $F_k$-integrable on $\sigma_k$; reason: the quantities $T_k$, $W_k$, $R_k$ are undefined otherwise (Lean's integral would be the junk value 0); only undefined cases are excluded
--   - generalization: D.3.1's standing assumptions (p. 56): $F_i$ has a bounded density, and state 2 dominates state 1 ($\exists\sigma_2$ with $\Delta(\sigma_2,\sigma_1)>0$ for all $\sigma_1$) → not assumed; reason: the claim is an algebraic property of $r$ that holds for all trip-length laws and payments, so it specializes to the source
-- source:
--   Garg, Nazerzadeh, Driver Surge Pricing, arXiv:1905.07544v4, p. 57, Remark 1 (bullet 4)

import Mathlib
import Definitions.Def_DriverSurge_IC_Pricing

namespace DriverSurge.IC

open MeasureTheory Set

/-- Remark 1, bullet 4 (p. 57; corrected: the sign change of `r` is at some `U ∈ [0, ∞]`, not
`U ∈ (0, ∞]`). For a policy `σ` with `w_k` and `τ` integrable on `σ_k`: if `Δ_{ji} < 0` and `w_i(u)/u` is
non-decreasing on `(0, ∞)`, then `r(u, i, w, σ)` is strictly increasing in `u > 0`, and it is negative
below some `U ∈ [0, ∞]` and positive above it. -/
theorem remark_1_increasing (P : Primitives) (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ)
    (hσ : IsPolicy σ) (hw : ∀ k, IntegrableOn (w k) (σ k) (P.F k))
    (hτ : ∀ k, IntegrableOn (fun τ : ℝ => τ) (σ k) (P.F k)) (i : Fin 2)
    (hΔ : stateRate P (other i) (w (other i)) (σ (other i)) - stateRate P i (w i) (σ i) < 0)
    (hmono : MonotoneOn (fun u : ℝ => w i u / u) (Ioi 0)) :
    StrictMonoOn (rFun P w σ i) (Ioi 0) ∧
    ∃ U : EReal, 0 ≤ U ∧
      (∀ u : ℝ, 0 < u → (u : EReal) < U → rFun P w σ i u < 0) ∧
      (∀ u : ℝ, 0 < u → U < (u : EReal) → 0 < rFun P w σ i u) := by sorry

end DriverSurge.IC
