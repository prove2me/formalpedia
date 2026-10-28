-- Prove2me | Theorems.Thm_DriverSurge_IC_lemma_8
-- name    : DriverSurge.IC.lemma_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:19.505217+00:00
-- url     : https://prove2.me/theorems/8d5c7eb3-cd74-428f-b832-7cd4af92bbda
-- title:
--   Lemma 8, p. 57 — for w_i(τ) = mτ + a with m > 0 > a, r(u, i, w, σ) is strictly quasi-concave in u whenever ∆_{ji} ≥ 0
-- statement:
--   Let the payment in state $i$ be negative affine, $w_i(\tau)=m\tau+a$ with $m>0$ and $a<0$. For every policy $\sigma$ (with $w_k$ and $\tau$ $F_k$-integrable on $\sigma_k$) such that
--   $$\Delta_{ji}=R_j(w_j,\sigma_j)-R_i(w_i,\sigma_i)\ge0,$$
--   the function $u\mapsto r(u,i,w,\sigma)$ is strictly quasi-concave on $(0,\infty)$: there is $U\in[0,\infty]$ such that its derivative is strictly positive on $(0,U)$ and strictly negative on $(U,\infty)$.
--
--   With Lemma 5 this gives the non-surge policy form $(t_2,t_3)$ under negative affine pricing.
--
--   **Formalization Note** Lean state `0` is the paper's non-surge state 1 and Lean state `1` the surge state 2; `other i` is the state $j\ne i$.
--
--   Differences from the source:
--   - reading: "strictly quasi-concave in $u$" → the mirror of p. 63's definition: derivative strictly positive on $(0,U)$, strictly negative on $(U,\infty)$, $U\in[0,\infty]$; reason: the paper defines strict quasi-convexity on p. 63 and uses quasi-concavity as its mirror image
--   - encoding: the formulas use $\int_{\sigma_k}\tau\,dF_k$ and $\int_{\sigma_k}w_k\,dF_k$ without saying they are finite → $\tau$ and $w_k$ are assumed $F_k$-integrable on $\sigma_k$; reason: the quantities $T_k$, $W_k$, $R_k$ are undefined otherwise (Lean's integral would be the junk value 0); only undefined cases are excluded
--   - generalization: D.3.1's standing assumptions (p. 56): $F_i$ has a bounded density, and state 2 dominates state 1 ($\exists\sigma_2$ with $\Delta(\sigma_2,\sigma_1)>0$ for all $\sigma_1$) → not assumed; reason: the claim is a property of $r$ as a function of $u$ that holds for all trip-length laws and payments, so it specializes to the source
-- source:
--   Garg, Nazerzadeh, Driver Surge Pricing, arXiv:1905.07544v4, p. 57, Lemma 8 (proof pp. 63–64)

import Mathlib
import Definitions.Def_DriverSurge_IC_Pricing

namespace DriverSurge.IC

open MeasureTheory Set

/-- Lemma 8 (p. 57). If `w_i(τ) = mτ + a` with `m > 0` and `a < 0`, then for every policy `σ` (with `w_j`
and `τ` integrable on `σ_j`, `σ_i`) where `Δ_{ji} ≥ 0`, `r(u, i, w, σ)` is strictly quasi-concave in
`u > 0` (its derivative is strictly positive up to a point and strictly negative above it). -/
theorem lemma_8 (P : Primitives) (w : Fin 2 → ℝ → ℝ) (i : Fin 2) (m a : ℝ) (hm : 0 < m)
    (ha : a < 0) (hwi : w i = fun τ => m * τ + a) (σ : Fin 2 → Set ℝ) (hσ : IsPolicy σ)
    (hw : ∀ k, IntegrableOn (w k) (σ k) (P.F k))
    (hτ : ∀ k, IntegrableOn (fun τ : ℝ => τ) (σ k) (P.F k))
    (hΔ : 0 ≤ stateRate P (other i) (w (other i)) (σ (other i)) - stateRate P i (w i) (σ i)) :
    StrictQuasiconcaveIoi (rFun P w σ i) := by sorry

end DriverSurge.IC
