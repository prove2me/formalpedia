-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_n_decomp
-- name    : Formalism.FourierDecayAlt.P.B2x6.n_decomp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:58:42.223922+00:00
-- url     : https://prove2.me/theorems/b95eb5b5-004f-46a6-8050-8aa10ae85440
-- title:
--   B2x6: n decomp
-- statement:
--   The B2x6 construction uses the n decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentHeisenbergDecomposition.lean#L354-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentHeisenbergDecomposition.lean#L354-L426

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}

theorem Formalism.FourierDecayAlt.P.B2x6.n_decomp {g : Mat k (1 + r')} (hg : g ∈ Nset k (1 + r')) :
    ∃ x : HPar k r', blk g ∈ Nset k r' ∧ g = heis0 k r' x * ιLev k 1 r' (blk g) := by sorry
