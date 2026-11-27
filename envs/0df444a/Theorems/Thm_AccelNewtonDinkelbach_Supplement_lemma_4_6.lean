-- Prove2me | Theorems.Thm_AccelNewtonDinkelbach_Supplement_lemma_4_6
-- name    : AccelNewtonDinkelbach.Supplement.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:04:23.140587+00:00
-- url     : https://prove2.me/theorems/6172f5f2-85f2-4d8a-9805-f92e98fd343d
-- title:
--   Lemma 4.6 — negative cycles and bicycles characterize $f(\delta)=-\infty$
-- statement:
--   For every $\delta\in\mathbb R$, the parametric value $f(\delta)$ equals $-\infty$ if and only if $D$ is nonempty and the graph with the outgoing arcs of $u$ removed contains a negative unit-gain cycle, a negative bicycle, or a $(\delta,u)$-negative flow-generating cycle.
--
--   Differences from the source:
--   - generalization: the full graph G before deleting δ⁺(u) → any active arc subgraph A before deleting the active outgoing arcs of u; reason: A equal to all arcs is the source instance and phase subgraphs use the same claim
--   - encoding: f(δ) = −∞ → the EReal parametric infimum equals ⊥; reason: same extended-real value
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Lemma 4.6, p.13

import Mathlib
import Definitions.Def_AccelNewtonDinkelbach_Supplement_M2VPICycles
import Definitions.Def_AccelNewtonDinkelbach_Supplement_M2VPIFractional

namespace AccelNewtonDinkelbach.Supplement

set_option autoImplicit false

/-- **Lemma 4.6 (when the parametric LP has value `−∞`).**
Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Lemma 4.6, p.13.
All cycles, bicycles, and paths are restricted to the active graph with the outgoing arcs of `u`
removed. -/
theorem lemma_4_6 {n m : ℕ} (M : M2VPI n m) (A : Fin m → Prop) (u : Fin n) (δ : ℝ) :
    M.paramF A u δ = ⊥ ↔
      (∃ x, M.InD A u x) ∧
      let B := fun e => A e ∧ M.tail e ≠ u
      (M.HasNegativeUnitGainCycle B ∨ M.HasNegativeBicycle B ∨
        M.HasDeltaNegativeGeneratingCycle B δ u) := by sorry

end AccelNewtonDinkelbach.Supplement
