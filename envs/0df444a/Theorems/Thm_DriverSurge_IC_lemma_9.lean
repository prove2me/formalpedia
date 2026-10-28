-- Prove2me | Theorems.Thm_DriverSurge_IC_lemma_9
-- name    : DriverSurge.IC.lemma_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:29.668444+00:00
-- url     : https://prove2.me/theorems/083aa0bc-2f38-444a-a1a9-0c065276af6f
-- title:
--   Lemma 9, p. 58 (corrected: R_1 ≥ 0) — for w_2 = mτ + zq_{2→1}(τ), m > R_1, and z/(m − R_1) in the window, r(u, 2, w, σ) > 0 for all u, σ_2; the window is nonempty
-- statement:
--   Fix a non-surge policy $\sigma_1$ and a payment $w_1$ integrable on it, with $Q_1=Q_1(\sigma_1)$, $T_1=T_1(\sigma_1)$ and $R_1=R_1(w_1,\sigma_1)\ge0$. Let $\bar Q_2$, $\bar T_2$ be the values of $Q_2$, $T_2$ at $\sigma_2=(0,\infty)$, assume finite means, and let $w_2(\tau)=m\tau+z\,q_{2\to1}(\tau)$ with $m>R_1$. If
--   $$\frac{T_1(\lambda_{2\to1}\bar T_2-\bar Q_2)-(Q_1+T_1\lambda_{2\to1})}{Q_1(\lambda_{2\to1}\bar T_2-\bar Q_2)+\lambda_{2\to1}(Q_1+T_1\lambda_{2\to1})}<\frac{z}{m-R_1}<\frac{\bar Q_2T_1+Q_1}{Q_1(\bar Q_2-\lambda_{2\to1})},$$
--   then $r(u,2,w,\sigma)>0$ for every $u>0$ and every open $\sigma_2\subseteq(0,\infty)$; hence $\partial R(w,\sigma)/\partial u>0$ wherever $f_2(u)>0$. Furthermore the constraint set is feasible regardless of the primitives: the lower bound is strictly below the upper bound.
--
--   Lemma 9 makes accepting every surge trip optimal; it is one half of the incentive-compatibility argument of Theorem 3.
--
--   **Formalization Note** Lean state `0` is the paper's non-surge state 1 and Lean state `1` the surge state 2; `other i` is the state $j\ne i$. The denominators are positive: $\lambda_{2\to1}\bar T_2-\bar Q_2\ge0$ and $\bar Q_2>\lambda_{2\to1}$ (Remark 4).
--
--   Differences from the source:
--   - correction: $R_1$ arbitrary → $R_1\ge0$ assumed; reason: the proof's step "$m/(m-R_1)>1$" (p. 66) needs $R_1\ge0$, and the lemma fails without it, even under D.3.1's standing assumptions: with $F_1=F_2=\mathrm{Exp}(1)$, $\lambda_1=1$, $\lambda_2=0.1$, $\lambda_{1\to2}=\lambda_{2\to1}=1$, $\sigma_1=(0,\infty)$, $w_1\equiv-1$ (so $R_1=-1/2$), $m=0.1$, $z/(m-R_1)=-0.468$ inside the window $(-0.935,76.5)$, and $\sigma_2=\emptyset$, one gets $r(0.001,2,w,\sigma)\approx-0.30<0$; state 2 dominates state 1 there, since $R_1(w_1,\sigma_1')\le0$ for every $\sigma_1'$ while $R_2(w_2,(2,\infty))\approx0.002>0$ (`checks/lemma9_counterexample_surge.py`)
--   - reading: "$\partial/\partial u R(w,\sigma)>0$, for all $u$" → $r(u,i,w,\sigma)>0$ for every $u>0$; reason: D.3.1 fixes $\propto$ as "same sign except where $f(u)=0$"; the proof (p. 65) establishes positivity of the $\propto$ expression
--   - reading: "the constraint set is feasible" → the lower end of the window is strictly below the upper end; reason: the proof (p. 66) shows exactly this inequality
--   - encoding: $\bar T_2$ implicitly finite → finite means; $w_1$ $F_1$-integrable on $\sigma_1$; reason: $\bar T_2$, $R_1$ are undefined otherwise; only undefined cases are excluded
--   - generalization: D.3.1's standing assumptions (p. 56): $F_i$ has a bounded density, and state 2 dominates state 1 ($\exists\sigma_2$ with $\Delta(\sigma_2,\sigma_1)>0$ for all $\sigma_1$) → not assumed; reason: the proof (pp. 65–66) is algebra on $r$ and does not use them (with $R_1\ge0$ the lemma held on every one of 300 random primitives × 30 random $\sigma_2$, `checks/lemma9_10_check.py`), so it specializes to the source
-- source:
--   Garg, Nazerzadeh, Driver Surge Pricing, arXiv:1905.07544v4, p. 58, Lemma 9 (proof pp. 65–66)

import Mathlib
import Definitions.Def_DriverSurge_IC_Pricing

namespace DriverSurge.IC

open MeasureTheory Set

/-- Lemma 9 (p. 58; corrected: `R_1 ≥ 0`). Fix a non-surge policy `s₁` (state 1 = Lean `0`) and a
payment `w_1` integrable on it, with `Q_1 = Q_1(s₁)`, `T_1 = T_1(s₁)`, `R_1 = R_1(w_1, s₁) ≥ 0`; let
`Q̄_2`, `T̄_2` be the surge-state values at `(0, ∞)`, and `w_2(τ) = mτ + zq_{2→1}(τ)` with `m > R_1`. If
`[T_1(λ_{2→1}T̄_2 − Q̄_2) − (Q_1 + T_1λ_{2→1})] / [Q_1(λ_{2→1}T̄_2 − Q̄_2) + λ_{2→1}(Q_1 + T_1λ_{2→1})] < z/(m − R_1) < (Q̄_2T_1 + Q_1)/(Q_1(Q̄_2 − λ_{2→1}))`,
then `r(u, 2, w, {s₁, s₂}) > 0` for every `u > 0` and every open `s₂ ⊆ (0, ∞)` (so `∂/∂u R(w, σ) > 0` in
the `∝` sense of D.3.1). Moreover the lower bound is below the upper bound (the constraint set is
feasible). -/
theorem lemma_9 (P : Primitives) (hmean : FiniteMean P) (w : Fin 2 → ℝ → ℝ) (s₁ : Set ℝ)
    (hs₁ : IsAdmissible s₁) (hw0 : IntegrableOn (w 0) s₁ (P.F 0)) (m z : ℝ)
    (hw1 : w 1 = fun τ => m * τ + z * q P 1 τ)
    (hR : 0 ≤ stateRate P 0 (w 0) s₁) (hm : stateRate P 0 (w 0) s₁ < m) :
    ((Tn P 0 s₁ * (P.sw 1 * Tn P 1 (Ioi 0) - Qn P 1 (Ioi 0)) - (Qn P 0 s₁ + Tn P 0 s₁ * P.sw 1)) /
          (Qn P 0 s₁ * (P.sw 1 * Tn P 1 (Ioi 0) - Qn P 1 (Ioi 0)) +
            P.sw 1 * (Qn P 0 s₁ + Tn P 0 s₁ * P.sw 1)) <
        z / (m - stateRate P 0 (w 0) s₁) →
      z / (m - stateRate P 0 (w 0) s₁) <
        (Qn P 1 (Ioi 0) * Tn P 0 s₁ + Qn P 0 s₁) / (Qn P 0 s₁ * (Qn P 1 (Ioi 0) - P.sw 1)) →
      ∀ s₂ : Set ℝ, IsAdmissible s₂ → ∀ u : ℝ, 0 < u → 0 < rFun P w ![s₁, s₂] 1 u) ∧
    (Tn P 0 s₁ * (P.sw 1 * Tn P 1 (Ioi 0) - Qn P 1 (Ioi 0)) - (Qn P 0 s₁ + Tn P 0 s₁ * P.sw 1)) /
          (Qn P 0 s₁ * (P.sw 1 * Tn P 1 (Ioi 0) - Qn P 1 (Ioi 0)) +
            P.sw 1 * (Qn P 0 s₁ + Tn P 0 s₁ * P.sw 1)) <
      (Qn P 1 (Ioi 0) * Tn P 0 s₁ + Qn P 0 s₁) / (Qn P 0 s₁ * (Qn P 1 (Ioi 0) - P.sw 1)) := by sorry

end DriverSurge.IC
