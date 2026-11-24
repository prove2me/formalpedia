-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallA_tendsto_card_of_le
-- name    : Formalism.HermitianLattices.Ext.L3.BallA.tendsto_card_of_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:07.213797+00:00
-- url     : https://prove2.me/theorems/c9a01511-9ff0-4e3c-af26-0c130d3bb286
-- title:
--   Ball A: tendsto card of le
-- statement:
--   The Ball A construction uses the tendsto card of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/DiscreteTopologyOfZsmul.lean#L115-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/DiscreteTopologyOfZsmul.lean#L115-L136

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscreteTopologyOfZsmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module ZSpan Filter Topology Pointwise Bornology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallA
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (μ : Measure E) [μ.IsAddHaarMeasure]

theorem Formalism.HermitianLattices.Ext.L3.BallA.tendsto_card_of_le (Λ₁ Λ : Submodule ℤ E) [DiscreteTopology Λ₁] [IsZLattice ℝ Λ₁]
    (hle : Λ₁ ≤ Λ) {N : ℤ} (hN : N ≠ 0) (h : ∀ y ∈ Λ, N • y ∈ Λ₁) {s : Set E}
    (hs₁ : IsBounded s) (hs₂ : MeasurableSet s) (hs₃ : Convex ℝ s) :
    Λ₁.toAddSubgroup.relIndex Λ.toAddSubgroup ≠ 0 ∧
    Tendsto (fun n : ℕ ↦ (Nat.card (s ∩ (n : ℝ)⁻¹ • Λ : Set E) : ℝ) / n ^ finrank ℝ E)
      atTop (𝓝 (μ.real s * (Λ₁.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) /
        ZLattice.covolume Λ₁ μ)) := by sorry
