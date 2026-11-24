-- Prove2me | Theorems.Thm_Formalism_REAL_pfil_succ_le_sup_map
-- name    : Formalism.REAL.pfil_succ_le_sup_map
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:24:35.145618+00:00
-- url     : https://prove2.me/theorems/80440dac-ac73-4f2c-96c4-6be6ebc24b17
-- title:
--   REAL: pfil succ le sup map
-- statement:
--   The REAL construction uses the pfil succ le sup map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L167-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L167-L184

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

theorem Formalism.REAL.pfil_succ_le_sup_map (j : ℕ) : pfil ε E u (j + 1) ≤
    pfil ε E u j ⊔ ⨆ p : Fin n × Fin n, (pfil ε E u j).map (E p.1 p.2) := by sorry
