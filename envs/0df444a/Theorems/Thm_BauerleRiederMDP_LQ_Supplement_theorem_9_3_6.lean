-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_9_3_6
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_9_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:06:35.459802+00:00
-- url     : https://prove2.me/theorems/21141a93-5c45-4813-9ba7-49f5fe5c0748
-- title:
--   Theorem 9.3.6 — uncontrolled drift: 'invest all the money in the bond' is optimal iff 𝔼Y ≤ 0
-- statement:
--   Let $\rho  = \mu _i$ for all $i = 1, \dots , d$. If $U$ is continuously differentiable and $U'(x + u \cdot  Y)Y$ is integrable for all $x > 0$ and $\|u\|$ small, then "invest all the money in the bond" is optimal if and only if $\mathbb E Y \le  0$.
--
--   **Formalization Note.** The subsection's standing hypothesis $\rho  = \mu _i$ for all $i$ is a hypothesis. $U$ is a utility function on $[0, \infty )$ with values in $\mathbb R _+$, continuously differentiable on $(0, \infty )$; the integrability is required for $u$ in the admissible set $U$ with $\|u\| < \delta (x)$. "Invest all the money in the bond" is the Markov strategy with fractions $0$; optimal means $V_{f_^*}(t, x) = V(t, x)$ at every $(t, x) \in  E$, $V$ the supremum over all predictable strategies. $\mathbb E Y \le  0$ is componentwise.
--
--   Differences from the source:
--   - reading: U′(x + u·Y)Y integrable for ‖u‖ small → for u in the admissible set U with ‖u‖ < δ(x); reason: only admissible u occur
--   - reading: U continuously differentiable → C^1 on (0,∞); reason: U is only defined on [0,∞); the derivative is used at positive wealth
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 9.3.6, p.289 (PDF 299)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_IsUtilityFunction
import Definitions.Def_BauerleRiederMDP_PDMDP_ControlFn
import Definitions.Def_BauerleRiederMDP_PDMDP_RelaxedControl
import Definitions.Def_BauerleRiederMDP_PDMDP_DecisionRule
import Definitions.Def_BauerleRiederMDP_PDMDP_StageModel
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Ufrac
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_flow
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_relaxedStage
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_stage
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_Jinf
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JMStrategy
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_state
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_Vstrat
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_V
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_markovJMStrategy
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_Eset

open MeasureTheory
open BauerleRiederMDP.PDMDP
open BauerleRiederMDP.RegimeSwitching (IsUtilityFunction)

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem 9.3.6** (uncontrolled drift) (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), Theorem 9.3.6, p.289, PDF 299, subsection "Uncontrolled Drift",
p.289). Let `ρ = μ_i` for all `i = 1, …, d`. If `U` is continuously differentiable and
`U′(x + u · Y)Y` is integrable for all `x > 0` and `‖u‖` small, then "invest all the money in the
bond" is optimal if and only if `𝔼Y ≤ 0`.

**Formalization Note.** The subsection's standing hypothesis `ρ = μ_i` for all `i` is a hypothesis.
`U` is a utility function on `[0, ∞)` with values in `ℝ_+`, continuously differentiable on
`(0, ∞)`; the integrability is required for `u` in the admissible set `U` with `‖u‖ < δ(x)`.
"Invest all the money in the bond" is the Markov strategy with fractions `0`; optimal means
`V_{f_*}(t, x) = V(t, x)` at every `(t, x) ∈ E`, `V` the supremum over all predictable strategies.
`𝔼Y ≤ 0` is componentwise. -/
theorem theorem_9_3_6 {d : ℕ} (Mk : JumpMarket d) (U : ℝ → ℝ)
    (hU : IsUtilityFunction U (Set.Ici 0)) (hU0 : ∀ x, 0 ≤ x → 0 ≤ U x)
    (hρ : ∀ i, Mk.μ i = Mk.ρ) (hC1 : ContDiffOn ℝ 1 U (Set.Ioi 0))
    (hint : ∀ x : ℝ, 0 < x → ∃ δ : ℝ, 0 < δ ∧ ∀ u : Ufrac d, ‖u.1‖ < δ →
      Integrable (fun y => deriv U (x + u.1 ⬝ᵥ y) • y) Mk.QY) :
    (∀ p ∈ Mk.Eset,
        Mk.Vstrat U (markovJMStrategy fun _ =>
          (⟨fun _ => ⟨0, fun _ => le_rfl, by simp⟩, measurable_const⟩ :
            DecisionRule (ℝ × ℝ) (Ufrac d))) p = Mk.V U p) ↔
      ∀ k, ∫ y, y k ∂Mk.QY ≤ 0 := by sorry

end BauerleRiederMDP.LQ.Supplement
