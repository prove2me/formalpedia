-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_sandwich
-- name    : Formalism.FourierDecayAlt.P.B2x3.sandwich
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:43:26.332395+00:00
-- url     : https://prove2.me/theorems/44f2f812-b1de-4631-aaef-863e5a200e02
-- title:
--   B2x3: sandwich
-- statement:
--   The B2x3 construction uses the sandwich property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L412-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L412-L431

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.B2x3.sandwich (a b N : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (M : Mat k r)
    (h1 : M * Em k r = Em k r * N) (h2 : (Em k r)ᵀ * M = N * (Em k r)ᵀ) :
    embWb k r a * M * embWb k r b =
      Em k r * (a * N * b) * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) * M * (1 - Em k r * (Em k r)ᵀ) := by sorry
