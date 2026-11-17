-- Prove2me | Theorems.Thm_EffHorizonProphet_Supplement_theorem_9
-- name    : EffHorizonProphet.Supplement.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:05:41.835129+00:00
-- url     : https://prove2.me/theorems/8e032988-4ef2-4fff-acfb-0c1809b8138e
-- title:
--   Theorem 9 — every infinite-horizon stopping rule has $\mathrm{CR}_\infty\le 1/(1+\tilde\gamma)$ under geometric discounting
-- statement:
--   Fix $0<\tilde\gamma<1$. Let $Y_1,Y_2,\dots$ be i.i.d. from an admissible base law $D$ ($D$ carried by $[0,\infty)$, $0<\mathbb E_D[Y]<\infty$) and $X_i=\tilde\gamma^{i-1}Y_i$. A stopping rule takes values in $\mathbb N\cup\{\infty\}$, with $X_\infty:=0$, and
--   $$\mathrm{CR}_\infty(\tau)=\inf_{D\in\mathcal D}\frac{\mathbb E_D[X_\tau]}{\mathbb E_D[\sup_{i\ge1}X_i]}.$$
--   Then every stopping policy satisfies
--   $$\mathrm{CR}_\infty(\tau)\le\frac1{1+\tilde\gamma}.$$
--
--   Precisely: for every $u>1/(1+\tilde\gamma)$ there is one admissible law $D$ on which every stopping rule earns at most $u\,\mathbb E_D[\sup_iX_i]$. This is Boshuizen's sharp prophet-to-optimal-stopping factor $1+\tilde\gamma$ for geometric discounting.
--
--   Differences from the source:
--   - generalization: every stopping policy $\tau$ satisfies $\mathrm{CR}_\infty(\tau)\le\frac1{1+\tilde\gamma}$ → for every $u>\frac1{1+\tilde\gamma}$ there is one admissible $D$ such that every stopping rule $\tau$ has $\mathbb E_D[X_\tau]\le u\,\mathbb E_D[\sup_iX_i]$; reason: this implies the bound for each fixed $\tau$ and also for policies that choose their rule knowing $D$; A.10 proves exactly this, on one two-point law for all rules
--   - generalization: a stopping rule is a stopping time for $\sigma(Y_1,\dots,Y_i)$ (A.5, p.33; A.10, p.50) → a stopping time for the stage pairs $(Y_j,U_j)_{j\le i}$ with independent uniform coins $U_j$, so randomized rules are included; reason: the class of rules is larger, so the upper bound for it contains the paper's bound for every non-randomized rule
--   - encoding: real-valued expectations of $X_\tau$ and $\sup_iX_i$ → lower Lebesgue integrals in $[0,\infty]$; reason: for an admissible law both are finite and the prophet value is positive (p.11), so nothing changes; it avoids junk values
--   - encoding: stages $i=1,2,\dots$ and $\tau=\infty$ for never stopping → stages $0,1,\dots$ and $\tau=\top$ in $\mathbb N\cup\{\top\}$; reason: a relabelling
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Theorem 9, p.12; proof in A.10, pp.47–52

import Mathlib
import Definitions.Def_EffHorizonProphet_IsAdmissible
import Definitions.Def_EffHorizonProphet_Supplement_IsInfStoppingRule
import Definitions.Def_EffHorizonProphet_Supplement_infStopReward
import Definitions.Def_EffHorizonProphet_Supplement_infProphet

open MeasureTheory
open scoped ENNReal

namespace EffHorizonProphet.Supplement

/-- **Theorem 9** (classical geometric-discount upper bound; Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), p.12; proof in A.10,
pp.47–52): for `0 < γ̃ < 1`, every stopping policy of the infinite-horizon model satisfies
`CR_∞(τ) ≤ 1/(1 + γ̃)`.

**Formalization Note** Stated as: for every `u > 1/(1 + γ̃)` there is one admissible law `D` on
which every stopping rule `τ` has `E_D[X_τ] ≤ u · E_D[sup_i X_i]`. This gives
`CR_∞(τ) = inf_D E_D[X_τ]/E_D[sup_i X_i] ≤ 1/(1 + γ̃)` for every `τ`, also for policies that choose
their stopping rule using `D`. Values are in `ℝ≥0∞`; stopping rules may use the independent coins
and may never stop (payoff `0`). -/
theorem theorem_9 {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {u : ℝ} (hu : 1 / (1 + γ) < u) :
    ∃ D : Measure ℝ, IsAdmissible D ∧
      ∀ τ, IsInfStoppingRule τ →
        infStopReward γ D τ ≤ ENNReal.ofReal u * infProphet γ D := by sorry

end EffHorizonProphet.Supplement
