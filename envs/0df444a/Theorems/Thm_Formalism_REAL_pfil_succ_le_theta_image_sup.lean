-- Prove2me | Theorems.Thm_Formalism_REAL_pfil_succ_le_theta_image_sup
-- name    : Formalism.REAL.pfil_succ_le_theta_image_sup
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:25:25.363177+00:00
-- url     : https://prove2.me/theorems/354a57ed-644a-4412-8319-0482e6bec7eb
-- title:
--   REAL: pfil succ le theta image sup
-- statement:
--   The REAL construction uses the pfil succ le theta image sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L586-L629
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L586-L629

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V)

theorem Formalism.REAL.pfil_succ_le_theta_image_sup (j : ℕ) : pfil ε E u (j + 1) ≤
    (arrV0 ε E u (j + 1)).map (thetaA E (j + 1)) ⊔ pfil ε E u j := by sorry
