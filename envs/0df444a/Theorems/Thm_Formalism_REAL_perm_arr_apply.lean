-- Prove2me | Theorems.Thm_Formalism_REAL_perm_arr_apply
-- name    : Formalism.REAL.perm_arr_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:25:08.818024+00:00
-- url     : https://prove2.me/theorems/77f6eb15-2355-4b9f-9b7d-051e6b8965cf
-- title:
--   REAL: perm arr apply
-- statement:
--   The REAL construction uses the perm arr apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L563-L565
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L563-L565

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

theorem Formalism.REAL.perm_arr_apply {j : ℕ} (σ : Equiv.Perm (Fin j)) (F : Arr V n j) (α : Fin j → Fin n × Fin n) :
    permArr V n σ F α = F (fun i => α (σ i)) := by sorry
