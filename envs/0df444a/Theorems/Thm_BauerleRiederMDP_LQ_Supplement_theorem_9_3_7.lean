-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_9_3_7
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_9_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:07:12.122685+00:00
-- url     : https://prove2.me/theorems/1c7f165a-ae7b-5ba6-b5e0-ed8b3e503a6e
-- title:
--   Theorem 9.3.7 — stability of the value and of optimal policies under approximation of the utility function
-- statement:
--   a) If $U$ and $\tilde U $ are two utility functions with value functions $V$ and $\tilde V $, then $\|V - \tilde V \|_b \le  \|U - \tilde U \|_b e^{T \bar{\mu}}/(1 - \alpha _b)$. b) Let $(U^{(n)})$ be utility functions with $\lim _{n\to \infty } \|U^{(n)} - U\|_b = 0$. Then $\emptyset  \ne  Ls A^*_n(t, x) \subset  A^*(t, x)$ for all $(t, x) \in  E$; in particular the limit $f^*$ of a sequence $(f^*_n)$ with $f^*_n(t, x) \in  A^*_n(t, x)$ for all $(t, x) \in  E$ defines an optimal stationary policy for the model with utility function $U$.
--
--   **Formalization Note.** $\gamma $ as in Theorem 9.3.4 ($\alpha _\gamma  < 1$); $\|\cdot \|_b$ is the weighted supremum norm on $E$ of $(t, x) \mapsto  U(x) - \tilde U (x)$ and of the (real) value functions, $b(t, x) = e^{\gamma (T-t)}(1 + x)$, $\bar{\mu} = \max {\mu _1, \dots , \mu _d, \rho }$. $A^*_n(t, x)$, $A^*(t, x)$ are sets of relaxed controls $\alpha  \in  R$ attaining $T^{(n)} V^{(n)}(t, x)$ and $T V(t, x)$ (operators over $R$, p.290). The limit $f^*$ is a relaxed decision rule, the pointwise limit of $f^*_n$ in the Young topology, and its stationary policy is optimal in the relaxed model, whose value is $V$.
--
--   Differences from the source:
--   - reading: the limit f* of (f*_n) → a pointwise limit in the Young topology of relaxed rules; optimal in the relaxed model whose value is V; reason: A*_n ⊂ R (p.290)
--   - reading: γ large enough → γ ≥ 0, γ + λ − μ̄ > 0, α_γ < 1; reason: standing choice of p.285
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 9.3.7, p.290 (PDF 300)

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
import Definitions.Def_MDPFinance_Contracting_LsSet
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_bfun
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_normb
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_IMcv
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_muBar
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_alphaGamma
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_alphaB
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_Treal

open Filter Topology
open BauerleRiederMDP.PDMDP
open BauerleRiederMDP.RegimeSwitching (IsUtilityFunction)
open MDPFinance.Contracting (LsSeq)

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem 9.3.7** (approximation of the utility function) (Bäuerle & Rieder, *Markov Decision
Processes with Applications to Finance* (2011), Theorem 9.3.7, p.290, PDF 300).
a) If `U` and `Ũ` are two utility functions with value functions `V` and `Ṽ`, then
`‖V − Ṽ‖_b ≤ ‖U − Ũ‖_b e^{T μ̄}/(1 − α_b)`.
b) Let `(U^{(n)})` be utility functions with `lim_{n→∞} ‖U^{(n)} − U‖_b = 0`. Then
`∅ ≠ Ls A*_n(t, x) ⊂ A*(t, x)` for all `(t, x) ∈ E`; in particular the limit `f*` of a sequence
`(f*_n)` with `f*_n(t, x) ∈ A*_n(t, x)` for all `(t, x) ∈ E` defines an optimal stationary policy for
the model with utility function `U`.

**Formalization Note.** `γ` as in Theorem 9.3.4 (`α_γ < 1`); `‖·‖_b` is the weighted supremum norm
on `E` of `(t, x) ↦ U(x) − Ũ(x)` and of the (real) value functions, `b(t, x) = e^{γ(T−t)}(1 + x)`,
`μ̄ = max{μ_1, …, μ_d, ρ}`. `A*_n(t, x)`, `A*(t, x)` are sets of relaxed controls `α ∈ R` attaining
`T^{(n)} V^{(n)}(t, x)` and `T V(t, x)` (operators over `R`, p.290). The limit `f*` is a relaxed
decision rule, the pointwise limit of `f*_n` in the Young topology, and its stationary policy is
optimal in the relaxed model, whose value is `V`. -/
theorem theorem_9_3_7 {d : ℕ} (Mk : JumpMarket d) (γ : ℝ) (hγ : 0 ≤ γ)
    (hγμ : 0 < γ + Mk.lam - Mk.muBar) (hαγ : Mk.alphaGamma γ < 1) :
    -- a)
    (∀ U Ut : ℝ → ℝ, IsUtilityFunction U (Set.Ici 0) → (∀ x, 0 ≤ x → 0 ≤ U x) →
      IsUtilityFunction Ut (Set.Ici 0) → (∀ x, 0 ≤ x → 0 ≤ Ut x) →
      Mk.normb γ (fun p => (Mk.V U p).toReal - (Mk.V Ut p).toReal) ≤
        Mk.normb γ (fun p => U p.2 - Ut p.2) * ENNReal.ofReal (Real.exp (Mk.T * Mk.muBar)) /
          (1 - Mk.alphaB γ)) ∧
    -- b)
    (∀ (U : ℝ → ℝ) (Us : ℕ → ℝ → ℝ), IsUtilityFunction U (Set.Ici 0) → (∀ x, 0 ≤ x → 0 ≤ U x) →
      (∀ n, IsUtilityFunction (Us n) (Set.Ici 0) ∧ ∀ x, 0 ≤ x → 0 ≤ Us n x) →
      Tendsto (fun n => Mk.normb γ (fun p => Us n p.2 - U p.2)) atTop (𝓝 0) →
      let Astar_n : ℕ → ℝ × ℝ → Set (RelaxedControl (Ufrac d)) := fun n p =>
        {α | (Mk.relaxedStage (Us n)).L (Mk.V (Us n)) p α =
          (Mk.relaxedStage (Us n)).T (Mk.V (Us n)) p}
      let Astar : ℝ × ℝ → Set (RelaxedControl (Ufrac d)) := fun p =>
        {α | (Mk.relaxedStage U).L (Mk.V U) p α = (Mk.relaxedStage U).T (Mk.V U) p}
      (∀ p ∈ Mk.Eset, (LsSeq fun n => Astar_n n p).Nonempty ∧
        LsSeq (fun n => Astar_n n p) ⊆ Astar p) ∧
      ∀ (fs : ℕ → RelaxedDecisionRule (ℝ × ℝ) (Ufrac d)) (f : RelaxedDecisionRule (ℝ × ℝ) (Ufrac d)),
        (∀ n, ∀ p ∈ Mk.Eset, (fs n).control p ∈ Astar_n n p) →
        (∀ p ∈ Mk.Eset, Tendsto (fun n => (fs n).control p) atTop (𝓝 (f.control p))) →
        ∀ p ∈ Mk.Eset, (Mk.relaxedStage U).Jinf (fun _ => f.control) p = Mk.V U p) := by sorry

end BauerleRiederMDP.LQ.Supplement
