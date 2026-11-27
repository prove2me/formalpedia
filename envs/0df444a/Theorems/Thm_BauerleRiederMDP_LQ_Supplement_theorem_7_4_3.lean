-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_7_4_3
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_7_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T23:58:37.33415+00:00
-- url     : https://prove2.me/theorems/e5d9a5d3-9096-5b62-9e1a-5dfe9f17abbf
-- title:
--   Theorem 7.4.3 (corrected: Borel spaces) — positive models: value iteration and the smallest r-superharmonic function
-- statement:
--   Let (C−) be satisfied (and the Integrability Assumption (A) of §7.4, $\varepsilon  < \infty $). Then a) $J_\infty  = T J_\infty $ and $J_\infty  = J$ (Value Iteration); b) $J_\infty $ is the smallest $r$-superharmonic function $v$ with $v \ge  -\varepsilon $, i.e. $J_\infty $ is the smallest function $v$ with $v \ge  T v$ and $v \ge  -\varepsilon $.
--
--   **Formalization Note.** $E$ and $A$ are standard Borel spaces and $D$ is a Borel subset of $E \times  A$ (the published model's `MeasurableSet D`), the setting "In what follows let $E$ and $A$ be Borel spaces" of §7.2 (p.199) on which the proof's appeal to Remark 2.3.14 rests; on general measurable spaces part a) is false (counterexample in `DISPROOF.md`). $J_\infty $, $J = \lim  J_n$, $T$, `Jinfpi` are the published `MDPFinance.Contracting` objects ($J_\infty (x) = +\infty $ is allowed). $J_\infty $ is in general only universally measurable; the integrals in $T$ are lower Lebesgue integrals of the positive and negative parts, which for universally measurable functions are the integrals with respect to the completed measures. In b) $v$ ranges over the universally measurable functions $E \to  [-\infty , \infty ]$.
--
--   Differences from the source:
--   - correction: general measurable state and action spaces → E and A standard Borel, D Borel; reason: false on general measurable spaces: A = ℝ with the discrete σ-algebra, from o the next state is y uniform on [0,1], reward 1{a = y} at y then absorption; J_∞(o) = 0 but T J_∞(o) = 1
--   - encoding: v ≥ T v, v ≥ −ε → v universally measurable, values in [−∞,∞]; reason: J_∞ is only universally measurable; the integrals are those of the completed measures
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 7.4.3, p.209 (PDF 220)

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_epsNeg
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_IntegrabilityAssumptionNeg
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_ConvergenceAssumptionCNeg
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_IsUniversallyMeasurable

open MeasureTheory ProbabilityTheory Filter
open MDPFinance.Contracting

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem 7.4.3** (corrected: Borel spaces) (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), Theorem 7.4.3, p.209, PDF 220). Let (C−) be satisfied (and the
Integrability Assumption (A) of §7.4, `ε < ∞`). Then
a) `J_∞ = T J_∞` and `J_∞ = J` (Value Iteration);
b) `J_∞` is the smallest `r`-superharmonic function `v` with `v ≥ −ε`, i.e. `J_∞` is the smallest
function `v` with `v ≥ T v` and `v ≥ −ε`.

**Formalization Note.** `E` and `A` are standard Borel spaces and `D` is a Borel subset of
`E × A` (the published model's `MeasurableSet D`), the setting "In what follows let `E` and `A` be
Borel spaces" of §7.2 (p.199) on which the proof's appeal to Remark 2.3.14 rests; on general
measurable spaces part a) is false (counterexample in `DISPROOF.md`). `J_∞`, `J = lim J_n`, `T`,
`Jinfpi` are the published `MDPFinance.Contracting` objects (`J_∞(x) = +∞` is allowed). `J_∞` is in
general only universally measurable; the integrals in `T` are lower Lebesgue integrals of the
positive and negative parts, which for universally measurable functions are the integrals with
respect to the completed measures. In b) `v` ranges over the universally measurable functions
`E → [−∞, ∞]`. -/
theorem theorem_7_4_3 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    [StandardBorelSpace E] [StandardBorelSpace A]
    (M : MarkovDecisionModel E A) (hA : IntegrabilityAssumptionNeg M)
    (hC : ConvergenceAssumptionCNeg M) :
    -- a) Value iteration
    (T M (Jinf M) = Jinf M ∧ Jinf M = Jlim M) ∧
    -- b) J_∞ is r-superharmonic with J_∞ ≥ −ε, and the smallest such function
    ((∀ x, T M (Jinf M) x ≤ Jinf M x) ∧ (∀ x, -epsNeg M x ≤ Jinf M x) ∧
      ∀ v : E → EReal, IsUniversallyMeasurable v → (∀ x, T M v x ≤ v x) →
        (∀ x, -epsNeg M x ≤ v x) → ∀ x, Jinf M x ≤ v x) := by sorry

end BauerleRiederMDP.LQ.Supplement
