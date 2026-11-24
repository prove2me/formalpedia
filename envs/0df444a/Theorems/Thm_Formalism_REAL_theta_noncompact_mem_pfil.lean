-- Prove2me | Theorems.Thm_Formalism_REAL_theta_noncompact_mem_pfil
-- name    : Formalism.REAL.theta_noncompact_mem_pfil
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:26:05.938624+00:00
-- url     : https://prove2.me/theorems/837ce98d-42b8-40cf-8c7d-506ec9fd252d
-- title:
--   REAL: theta noncompact mem pfil
-- statement:
--   The REAL construction uses the theta noncompact mem pfil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L574-L584
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L574-L584

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

theorem Formalism.REAL.theta_noncompact_mem_pfil (j : ℕ) (F : Arr V n j) (hF : F ∈ arrV0 ε E u j) :
    thetaA E j F ∈ pfil ε E u j := by sorry
