-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_heis_F
-- name    : Formalism.FourierDecayAlt.P.B2x6.heis_F
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:04:03.925437+00:00
-- url     : https://prove2.me/theorems/bbbfa5b3-9e16-4917-9cad-e415d78b2791
-- title:
--   B2x6: heis F
-- statement:
--   The B2x6 construction uses the heis F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentHeisenbergDecomposition.lean#L259-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentHeisenbergDecomposition.lean#L259-L262

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

theorem Formalism.FourierDecayAlt.P.B2x6.heis_F (x : HPar k r') (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    (heis0 k r' x *ᵥ u) (iF k r') = u (iF k r') - herm (Hpk k r') (res u) x.1 + u (iL k r') * hb k r' x.1 x.2 := by sorry
