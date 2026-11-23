-- Prove2me | Theorems.Thm_Formalism_F_exists_short_vector_of_isZLattice
-- name    : Formalism.F.exists_short_vector_of_isZLattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:42.900804+00:00
-- url     : https://prove2.me/theorems/83835cf3-d1f5-4c43-82c8-c9b5f83dfefd
-- title:
--   F: exists short vector of is ZLattice
-- statement:
--   The F construction uses the exists short vector of is ZLattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/ShortVector.lean#L27-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/ShortVector.lean#L27-L115

import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_ShortVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule MeasureTheory
noncomputable section
open Formalism Formalism.F
universe u

theorem Formalism.F.exists_short_vector_of_isZLattice (hC : CovolEqCovolume.{u}) {W : Type u} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (L : Submodule ℤ W) [DiscreteTopology L] [IsZLattice ℝ L] (hn : 0 < finrank ℝ W) :
    ∃ x ∈ L, x ≠ 0 ∧
      ‖x‖ ≤ Real.sqrt (finrank ℝ W : ℝ) * covol L ^ ((1 : ℝ) / (finrank ℝ W : ℝ)) := by sorry
