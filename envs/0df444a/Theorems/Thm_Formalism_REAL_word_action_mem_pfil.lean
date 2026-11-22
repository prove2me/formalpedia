-- Prove2me | Theorems.Thm_Formalism_REAL_word_action_mem_pfil
-- name    : Formalism.REAL.word_action_mem_pfil
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:03:52.308351+00:00
-- url     : https://prove2.me/theorems/d58534f6-338d-4dcd-b389-bef7f21a43db
-- title:
--   REAL: word action mem pfil
-- statement:
--   The REAL construction uses the word action mem pfil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L50-L53

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

theorem Formalism.REAL.word_action_mem_pfil (j : ℕ) (w : List (Fin n × Fin n)) (hw : w.length ≤ j)
    (hnc : ∀ p ∈ w, ε p.1 ≠ ε p.2) (y : V) (hy : y ∈ kSpan ε E u) : ew E w y ∈ pfil ε E u j := by sorry
