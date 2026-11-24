-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallA_volume_image_equivFun
-- name    : Formalism.HermitianLattices.Ext.L3.BallA.volume_image_equivFun
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:37.575809+00:00
-- url     : https://prove2.me/theorems/61988e6c-b6e3-4525-bcad-1973f7a0408b
-- title:
--   Ball A: volume image equiv Fun
-- statement:
--   The Ball A construction uses the volume image equiv Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/DiscreteTopologyOfZsmul.lean#L47-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/DiscreteTopologyOfZsmul.lean#L47-L63

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

theorem Formalism.HermitianLattices.Ext.L3.BallA.volume_image_equivFun {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) (s : Set E) :
    volume ((b.ofZLatticeBasis ℝ L).equivFun '' s) =
      μ s / ENNReal.ofReal (ZLattice.covolume L μ) := by sorry
