-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x5_lattice_of_index
-- name    : Formalism.FourierDecayAlt.P.S6x5.lattice_of_index
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:39.649824+00:00
-- url     : https://prove2.me/theorems/fa4a973d-d422-4598-81a2-a2be1a0528bf
-- title:
--   S6x5: lattice of index
-- statement:
--   The S6x5 construction uses the lattice of index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwistedIsRealOrderLattice.lean#L94-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwistedIsRealOrderLattice.lean#L94-L121

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x5
open Module MeasureTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem Formalism.FourierDecayAlt.P.S6x5.lattice_of_index (μ : Measure V) [μ.IsAddHaarMeasure] (M₁ M₂ : Submodule ℤ V)
    [DiscreteTopology M₁] [IsZLattice ℝ M₁] (h : M₁ ≤ M₂)
    (hn : M₁.toAddSubgroup.relIndex M₂.toAddSubgroup ≠ 0) (c : ℝ) (hc : c ≠ 0) :
    DiscreteTopology (M₂.map (scal V c)) ∧
    Submodule.span ℝ (M₂.map (scal V c) : Set V) = ⊤ ∧
    ZLattice.covolume (M₂.map (scal V c)) μ =
      |c| ^ finrank ℝ V * ZLattice.covolume M₁ μ /
        (M₁.toAddSubgroup.relIndex M₂.toAddSubgroup : ℝ) := by sorry
