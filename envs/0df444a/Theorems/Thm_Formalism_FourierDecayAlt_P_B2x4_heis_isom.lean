-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_heis_isom
-- name    : Formalism.FourierDecayAlt.P.B2x4.heis_isom
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:56:32.3738+00:00
-- url     : https://prove2.me/theorems/b972825d-8a70-44e3-97d4-0edf63a12b01
-- title:
--   B2x4: heis isom
-- statement:
--   The B2x4 construction uses the heis isom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConjugationInvarianceEverySetting.lean#L63-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConjugationInvarianceEverySetting.lean#L63-L70

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)

theorem Formalism.FourierDecayAlt.P.B2x4.heis_isom (hH : Hᴴ = H) (e v : Fin m → ℂ) (b : ℂ) (hee : herm H e e = 0) (hve : herm H v e = 0)
    (hb : b + star b + herm H v v = 0) (u w : Fin m → ℂ) :
    herm H (u - herm H u v • e + herm H u e • (v + b • e)) (w - herm H w v • e + herm H w e • (v + b • e)) =
      herm H u w := by sorry
