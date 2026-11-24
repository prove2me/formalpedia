-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_real_bound
-- name    : Formalism.FourierDecayAlt.P.B2x3.real_bound
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:04:10.553239+00:00
-- url     : https://prove2.me/theorems/1867aacb-3ee0-4234-8b96-5fb68f4af9b2
-- title:
--   B2x3: real bound
-- statement:
--   The B2x3 construction uses the real bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L669-L721
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L669-L721

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

theorem Formalism.FourierDecayAlt.P.B2x3.real_bound (u z : Fin (k + 1) → ℂ) (τ : ℝ)
    (h1 : (∑ i : Fin k, ‖u i.castSucc‖ ^ 2) - ‖u (Fin.last k)‖ ^ 2 ≤ 1)
    (h2 : ‖(∑ i : Fin k, star (z i.castSucc) * u i.castSucc) - star (z (Fin.last k)) * u (Fin.last k)‖ ≤ τ)
    (hT : (∑ i : Fin k, ‖z i.castSucc‖ ^ 2) < ‖z (Fin.last k)‖ ^ 2) (i : Fin (k + 1)) :
    ‖u i‖ ≤ 1 + (τ + √(∑ i : Fin k, ‖z i.castSucc‖ ^ 2)) / (‖z (Fin.last k)‖ - √(∑ i : Fin k, ‖z i.castSucc‖ ^ 2)) := by sorry
