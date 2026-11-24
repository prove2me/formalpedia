-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallA_discreteTopology_of_zsmul
-- name    : Formalism.HermitianLattices.Ext.L3.BallA.discreteTopology_of_zsmul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:10.041501+00:00
-- url     : https://prove2.me/theorems/0f36017b-883b-42ab-a397-aa4fe6d49c25
-- title:
--   Ball A: discrete Topology of zsmul
-- statement:
--   The Ball A construction uses the discrete Topology of zsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/DiscreteTopologyOfZsmul.lean#L105-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/DiscreteTopologyOfZsmul.lean#L105-L113

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

theorem Formalism.HermitianLattices.Ext.L3.BallA.discreteTopology_of_zsmul {Λ₁ Λ : Submodule ℤ E} [DiscreteTopology Λ₁] {N : ℤ}
    (hN : N ≠ 0) (h : ∀ y ∈ Λ, N • y ∈ Λ₁) : DiscreteTopology Λ := by sorry
