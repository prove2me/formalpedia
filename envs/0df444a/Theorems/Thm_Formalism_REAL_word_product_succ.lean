-- Prove2me | Theorems.Thm_Formalism_REAL_word_product_succ
-- name    : Formalism.REAL.word_product_succ
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:26:02.885563+00:00
-- url     : https://prove2.me/theorems/4806b917-3c09-47fc-a0d4-c7f41380b5ad
-- title:
--   REAL: word product succ
-- statement:
--   The REAL construction uses the word product succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L458-L462
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L458-L462

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
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

theorem Formalism.REAL.word_product_succ (E : Fin n → Fin n → Module.End ℂ V) {j : ℕ} (α : Fin (j + 1) → Fin n × Fin n) :
    u1W E α = E (α (Fin.last j)).1 (α (Fin.last j)).2 * u1W E (Fin.init α) := by sorry
