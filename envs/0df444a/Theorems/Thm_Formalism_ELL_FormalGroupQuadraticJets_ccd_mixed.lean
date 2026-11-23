-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_ccd_mixed
-- name    : Formalism.ELL.FormalGroupQuadraticJets.ccd_mixed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:49.47784+00:00
-- url     : https://prove2.me/theorems/ae6ee669-f9a2-478d-aa38-00448088ca53
-- title:
--   Formal Group Quadratic Jets: ccd mixed
-- statement:
--   The Formal Group Quadratic Jets construction uses the ccd mixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L130-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L130-L134

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.FormalGroupQuadraticJets
open Formalism.G.LogCR
variable {K : Type*} [CommRing K]

theorem Formalism.ELL.FormalGroupQuadraticJets.ccd_mixed (F : MvPowerSeries (Fin 2) K) :
    ccd 1 (MvPowerSeries.pderiv K 0 F) = ccd 0 (MvPowerSeries.pderiv K 1 F) := by sorry
