-- Prove2me | Theorems.Thm_DriverSurge_IC_lemma_7
-- name    : DriverSurge.IC.lemma_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:18.047652+00:00
-- url     : https://prove2.me/theorems/7d02ec51-59fc-40b9-ae3c-2ca7a12097a7
-- title:
--   Lemma 7, p. 57 — for w_i(τ) = mτ + a with m, a > 0, r(u, i, w, σ) is strictly quasi-convex in u whenever ∆_{ji} ≤ 0
-- statement:
--   Let the payment in state $i$ be positive affine, $w_i(\tau)=m\tau+a$ with $m>0$ and $a>0$. For every policy $\sigma$ (with $w_k$ and $\tau$ $F_k$-integrable on $\sigma_k$) such that
--   $$\Delta_{ji}=R_j(w_j,\sigma_j)-R_i(w_i,\sigma_i)\le0,$$
--   the function $u\mapsto r(u,i,w,\sigma)$ is strictly quasi-convex on $(0,\infty)$: there is $U\in[0,\infty]$ such that its derivative is strictly negative on $(0,U)$ and strictly positive on $(U,\infty)$.
--
--   With Lemma 5 this gives the surge-state policy form $(0,t_5)\cup(t_6,\infty)$ under positive affine pricing.
--
--   **Formalization Note** Lean state `0` is the paper's non-surge state 1 and Lean state `1` the surge state 2; `other i` is the state $j\ne i$.
--
--   Differences from the source:
--   - reading: "strictly quasi-convex in $u$" → the definition of p. 63: the derivative in $u$ is strictly negative on $(0,U)$ and strictly positive on $(U,\infty)$ for some $U\in[0,\infty]$; reason: the paper's own definition (proof of Lemma 7, p. 63), with the turning point allowed at $0$ or $\infty$
--   - encoding: the formulas use $\int_{\sigma_k}\tau\,dF_k$ and $\int_{\sigma_k}w_k\,dF_k$ without saying they are finite → $\tau$ and $w_k$ are assumed $F_k$-integrable on $\sigma_k$; reason: the quantities $T_k$, $W_k$, $R_k$ are undefined otherwise (Lean's integral would be the junk value 0); only undefined cases are excluded
--   - generalization: D.3.1's standing assumptions (p. 56): $F_i$ has a bounded density, and state 2 dominates state 1 ($\exists\sigma_2$ with $\Delta(\sigma_2,\sigma_1)>0$ for all $\sigma_1$) → not assumed; reason: the claim is a property of $r$ as a function of $u$ that holds for all trip-length laws and payments, so it specializes to the source
-- source:
--   Garg, Nazerzadeh, Driver Surge Pricing, arXiv:1905.07544v4, p. 57, Lemma 7 (proof p. 63)

import Mathlib
import Definitions.Def_DriverSurge_IC_Pricing

namespace DriverSurge.IC

open MeasureTheory Set

/-- Lemma 7 (p. 57). If `w_i(τ) = mτ + a` with `m, a > 0`, then for every policy `σ` (with `w_j` and `τ`
integrable on `σ_j`, `σ_i`) where `Δ_{ji} ≤ 0`, `r(u, i, w, σ)` is strictly quasi-convex in `u > 0` (its
derivative is strictly negative up to a point and strictly positive above it). -/
theorem lemma_7 (P : Primitives) (w : Fin 2 → ℝ → ℝ) (i : Fin 2) (m a : ℝ) (hm : 0 < m)
    (ha : 0 < a) (hwi : w i = fun τ => m * τ + a) (σ : Fin 2 → Set ℝ) (hσ : IsPolicy σ)
    (hw : ∀ k, IntegrableOn (w k) (σ k) (P.F k))
    (hτ : ∀ k, IntegrableOn (fun τ : ℝ => τ) (σ k) (P.F k))
    (hΔ : stateRate P (other i) (w (other i)) (σ (other i)) - stateRate P i (w i) (σ i) ≤ 0) :
    StrictQuasiconvexIoi (rFun P w σ i) := by sorry

end DriverSurge.IC
