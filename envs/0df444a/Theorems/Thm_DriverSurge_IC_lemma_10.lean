-- Prove2me | Theorems.Thm_DriverSurge_IC_lemma_10
-- name    : DriverSurge.IC.lemma_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:20.879392+00:00
-- url     : https://prove2.me/theorems/4485e131-6045-4206-b911-fd029c4a8657
-- title:
--   Lemma 10, p. 58 (corrected: R_2 > 0) — for w_1 = R_2τ + zq_{1→2}(τ) and z/R_2 in the window, r(u, 1, w, σ) > 0 for all u, σ_1; the window is nonempty
-- statement:
--   Fix a surge policy $\sigma_2$ and a payment $w_2$ integrable on it, with $Q_2=Q_2(\sigma_2)$, $T_2=T_2(\sigma_2)$ and $R_2=R_2(w_2,\sigma_2)>0$. Let $\bar Q_1$, $\bar T_1$ be the values of $Q_1$, $T_1$ at $\sigma_1=(0,\infty)$, assume finite means, and let $w_1(\tau)=m\tau+z\,q_{1\to2}(\tau)$ with $m=R_2$. If
--   $$-\frac{T_2\lambda_{1\to2}+Q_2}{Q_2(\lambda_{1\to2}\bar T_1-\bar Q_1)+\lambda_{1\to2}(T_2\lambda_{1\to2}+Q_2)}<\frac{z}{R_2}<\frac{1}{\bar Q_1-\lambda_{1\to2}},$$
--   then $r(u,1,w,\sigma)>0$ for every $u>0$ and every open $\sigma_1\subseteq(0,\infty)$; hence $\partial R(w,\sigma)/\partial u>0$ wherever $f_1(u)>0$. Furthermore the constraint set is feasible regardless of the primitives: the lower bound is strictly below the upper bound.
--
--   Lemma 10 makes accepting every non-surge trip optimal; with Lemma 9 it yields the incentive-compatible prices of Theorem 3, and the constant $C$ is what its window imposes on $R_1/R_2$.
--
--   **Formalization Note** Lean state `0` is the paper's non-surge state 1 and Lean state `1` the surge state 2; `other i` is the state $j\ne i$. The denominators are positive: $\lambda_{1\to2}\bar T_1-\bar Q_1\ge0$ and $\bar Q_1>\lambda_{1\to2}$ (Remark 4).
--
--   Differences from the source:
--   - correction: $R_2=R_2(w_2,\sigma_2)$ for an arbitrary $\sigma_2$ and $w_2$, of any sign; the window divides by $R_2$ → $R_2>0$ assumed; reason: for $R_2<0$ the lemma fails: $z=0$ lies in the window (its lower end is negative, its upper end positive) and Remark 2 gives $uT_1T_2\,r(u,1,w,\sigma)=R_2\,(q_{1\to2}(u)T_2+uQ_2)<0$ for every $u>0$ and every $\sigma_1$; e.g. all rates $1$, $F_1=F_2=\mathrm{Exp}(1)$, $w_2(\tau)=1-\tau^2$, $\sigma_2=(0,\infty)$ (so $R_2=-1/2$) and $w_1(\tau)=R_2\tau$, where state 2 dominates state 1 because $R_1\le0$ for every $\sigma_1$ while $R_2(w_2,(0,1))>0$; at $R_2=0$ the quotient $z/R_2$ is undefined (Lean's $z/0=0$ would be junk)
--   - reading: "$\partial/\partial u R(w,\sigma)>0$, for all $u$" → $r(u,i,w,\sigma)>0$ for every $u>0$; reason: D.3.1 fixes $\propto$ as "same sign except where $f(u)=0$"; the proof (p. 65) establishes positivity of the $\propto$ expression
--   - reading: "the constraint set is feasible" → the lower end of the window is strictly below the upper end; reason: the meaning in the proof of Lemma 9, mirrored
--   - encoding: $\bar T_1$ implicitly finite → finite means; $w_2$ $F_2$-integrable on $\sigma_2$; reason: $\bar T_1$, $R_2$ are undefined otherwise; only undefined cases are excluded
--   - generalization: D.3.1's standing assumptions (p. 56): $F_i$ has a bounded density, and state 2 dominates state 1 ($\exists\sigma_2$ with $\Delta(\sigma_2,\sigma_1)>0$ for all $\sigma_1$) → not assumed; reason: the proof (p. 66) is algebra on $r$ and does not use them (the lemma held on every one of 300 random primitives × 30 random $\sigma_1$, `checks/lemma9_10_check.py`), so it specializes to the source
-- source:
--   Garg, Nazerzadeh, Driver Surge Pricing, arXiv:1905.07544v4, p. 58, Lemma 10 (proof pp. 66–67)

import Mathlib
import Definitions.Def_DriverSurge_IC_Pricing

namespace DriverSurge.IC

open MeasureTheory Set

/-- Lemma 10 (p. 58). Fix a surge policy `s₂` (state 2 = Lean `1`) and a payment `w_2` integrable on it,
with `Q_2 = Q_2(s₂)`, `T_2 = T_2(s₂)` and `R_2 = R_2(w_2, s₂) > 0`; let `Q̄_1`, `T̄_1` be the non-surge
values at `(0, ∞)`, and `w_1(τ) = mτ + zq_{1→2}(τ)` with `m = R_2`. If
`−(T_2λ_{1→2} + Q_2) / [Q_2(λ_{1→2}T̄_1 − Q̄_1) + λ_{1→2}(T_2λ_{1→2} + Q_2)] < z/R_2 < 1/(Q̄_1 − λ_{1→2})`,
then `r(u, 1, w, {s₁, s₂}) > 0` for every `u > 0` and every open `s₁ ⊆ (0, ∞)` (so `∂/∂u R(w, σ) > 0` in
the `∝` sense of D.3.1). Moreover the lower bound is below the upper bound (the constraint set is
feasible). -/
theorem lemma_10 (P : Primitives) (hmean : FiniteMean P) (w : Fin 2 → ℝ → ℝ) (s₂ : Set ℝ)
    (hs₂ : IsAdmissible s₂) (hw1 : IntegrableOn (w 1) s₂ (P.F 1)) (z : ℝ)
    (hR : 0 < stateRate P 1 (w 1) s₂)
    (hw0 : w 0 = fun τ => stateRate P 1 (w 1) s₂ * τ + z * q P 0 τ) :
    (-(Tn P 1 s₂ * P.sw 0 + Qn P 1 s₂) /
          (Qn P 1 s₂ * (P.sw 0 * Tn P 0 (Ioi 0) - Qn P 0 (Ioi 0)) +
            P.sw 0 * (Tn P 1 s₂ * P.sw 0 + Qn P 1 s₂)) <
        z / stateRate P 1 (w 1) s₂ →
      z / stateRate P 1 (w 1) s₂ < 1 / (Qn P 0 (Ioi 0) - P.sw 0) →
      ∀ s₁ : Set ℝ, IsAdmissible s₁ → ∀ u : ℝ, 0 < u → 0 < rFun P w ![s₁, s₂] 0 u) ∧
    -(Tn P 1 s₂ * P.sw 0 + Qn P 1 s₂) /
          (Qn P 1 s₂ * (P.sw 0 * Tn P 0 (Ioi 0) - Qn P 0 (Ioi 0)) +
            P.sw 0 * (Tn P 1 s₂ * P.sw 0 + Qn P 1 s₂)) <
      1 / (Qn P 0 (Ioi 0) - P.sw 0) := by sorry

end DriverSurge.IC
