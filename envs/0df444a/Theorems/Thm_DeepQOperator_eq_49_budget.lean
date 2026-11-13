-- Prove2me | Theorems.Thm_DeepQOperator_eq_49_budget
-- name    : DeepQOperator.eq_49_budget
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:08:58.03772+00:00
-- url     : https://prove2.me/theorems/a5db5593-c5b1-4ffd-bfe3-af327e4dbeb5
-- title:
--   (49) and E.4: the sampling and direct raw protocols, their hard budgets and regret
-- statement:
--   Let $m\ge2$, $0<\gamma<1$, $\varepsilon>0$, and $\delta,R,v$ as in (8).
--   1. The sampling protocol of Appendix E.2–E.3 is raw, has at most two stages, uses the uniform quantizers (41), is measurable, and uses at most $5120R+2\min(m,64)v$ reply bits on every input of $P_{cb}$ and every seed, including failed estimates. For each fixed input $\theta\in P_{cb}$,
--   $$\mathbb E\,\ell\le\frac{33\varepsilon}{128}+\frac{\gamma}{32}\Pr(G^c)\le\frac{97\varepsilon}{128}.\tag{49}$$
--   2. The direct protocol of Appendix E.4, which reads all $m$ baseline scores and all $m$ payloads with $j_v$, is raw, fixed, uses the uniform quantizers, is measurable, costs $2mv$ bits, and has loss at most $33\varepsilon/128$ on every input and seed.
--
--   Selecting the protocol with the smaller declared budget gives (9).
--
--   **Formalization Note** The protocols are the definitions `samplingProtocol` (seed: uniform list of draws) and `directProtocol` (one-point seed). Regret is computed from the run with fuel equal to the budget.
--
--   Differences from the source:
--   - encoding: a reply of length d ≥ 0 bits in an alphabet of size at most 2^d → every asked field has length ≥ 1 and its symbol lies in {0, …, 2^d − 1}; reason: App. A: "A zero-bit reply is constant and can be removed"; an alphabet of size at most 2^d is a subset of {0, …, 2^d − 1}
--   - encoding: "the sum of lengths is at most B on every input and random path" → HardBudgetOn (Pcb m) B: for every θ ∈ P_cb, every seed ω and every number of steps, the charged lengths along the run total at most B; regret is computed from the run with fuel B; reason: same condition; with lengths ≥ 1 the run asks at most B fields
--   - encoding: Eℓ ≤ … ≤ 97ε/128 < ε → the lower Lebesgue integral of the loss is at most 97ε/128; reason: the intermediate terms are the proof; 97ε/128 < ε is arithmetic
--   - encoding: "return a fixed action"; candidates requested "for each i ∈ J" → the overflow action is −; candidates are read in increasing index order; reason: the paper leaves both choices free; neither affects the claims
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix E.3–E.4, eq. (49), p.25 (PDF p.28)

import Mathlib
import Definitions.Def_DeepQOperator_Family
import Definitions.Def_DeepQOperator_Quantizer
import Definitions.Def_DeepQOperator_ReplyProtocol
import Definitions.Def_DeepQOperator_Sampling

open MeasureTheory

namespace DeepQOperator

/-- **(49) and Appendix E.4: the two raw protocols of (9)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix E.3–E.4, p.25, PDF p.28).

Let `m ≥ 2`, `0 < γ < 1`, `ε > 0`, and `δ, R, v` as in (8).
1. The sampling protocol of E.2–E.3 is raw, has at most two stages, uses the uniform quantizers (41),
   is measurable, uses at most `5120R + 2 min(m, 64)v` reply bits on every input and seed (including
   failed estimates), and for each fixed full input has `Eℓ ≤ 97ε/128` (49).
2. The direct protocol of E.4, reading all `m` baseline scores and all `m` payloads with `j_v`, is raw,
   fixed, uses the uniform quantizers, is measurable, costs `2mv` bits, and has regret at most
   `33ε/128` on every input.

**Formalization Note.** The protocols are `samplingProtocol m γ ε` with the uniform seed law
`samplingSeedLaw m R` and `directProtocol m γ ε` with the Dirac law on `Unit`
(`Def_DeepQOperator_Sampling`). Regret is computed with fuel equal to the budget. -/
theorem eq_49_budget (m : ℕ) (hm : 2 ≤ m) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (ε : ℝ)
    (hε : 0 < ε) :
    (IsRaw (samplingProtocol m γ ε) ∧ (samplingProtocol m γ ε).IsAtMostTwoStage ∧
      UsesUniformQuantizers (samplingProtocol m γ ε) ∧ (samplingProtocol m γ ε).IsMeasurable ∧
      (samplingProtocol m γ ε).HardBudgetOn (Pcb m)
        (5120 * RParam m γ ε + 2 * min m 64 * vParam γ ε) ∧
      ∀ θ ∈ Pcb m,
        ∫⁻ ω, ENNReal.ofReal (loss m γ ((samplingProtocol m γ ε).decision
            (5120 * RParam m γ ε + 2 * min m 64 * vParam γ ε) θ ω) θ)
          ∂(samplingSeedLaw m (RParam m γ ε)) ≤ ENNReal.ofReal (97 * ε / 128)) ∧
    (IsRaw (directProtocol m γ ε) ∧ (directProtocol m γ ε).IsFixed ∧
      UsesUniformQuantizers (directProtocol m γ ε) ∧ (directProtocol m γ ε).IsMeasurable ∧
      (directProtocol m γ ε).HardBudgetOn (Pcb m) (2 * m * vParam γ ε) ∧
      ∀ θ ∈ Pcb m, ∀ ω : Unit,
        loss m γ ((directProtocol m γ ε).decision (2 * m * vParam γ ε) θ ω) θ ≤ 33 * ε / 128) := by sorry

end DeepQOperator
