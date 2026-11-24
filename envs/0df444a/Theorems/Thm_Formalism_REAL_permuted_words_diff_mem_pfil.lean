-- Prove2me | Theorems.Thm_Formalism_REAL_permuted_words_diff_mem_pfil
-- name    : Formalism.REAL.permuted_words_diff_mem_pfil
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:24:36.69752+00:00
-- url     : https://prove2.me/theorems/4bea7c7e-5a08-45cc-8ba8-efbdb685332c
-- title:
--   REAL: permuted words diff mem pfil
-- statement:
--   The REAL construction uses the permuted words diff mem pfil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L634-L691
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L634-L691

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

theorem Formalism.REAL.permuted_words_diff_mem_pfil (hE : GlRel E) (y : V) (hy : y ∈ kSpan ε E u) :
    ∀ l1 l2 : List (Fin n × Fin n), l1.Perm l2 → (∀ p ∈ l1, ε p.1 ≠ ε p.2) →
      ∀ m, l1.length = m + 1 → ew E l1 y - ew E l2 y ∈ pfil ε E u m := by sorry
