-- Prove2me | Theorems.Thm_Formalism_REAL_compact_generator_word_mem_pfil
-- name    : Formalism.REAL.compact_generator_word_mem_pfil
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:14.475687+00:00
-- url     : https://prove2.me/theorems/8f4aa935-3213-4d72-a2e2-db74de1c01f2
-- title:
--   REAL: compact generator word mem pfil
-- statement:
--   The REAL construction uses the compact generator word mem pfil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L86-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L86-L127

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

theorem Formalism.REAL.compact_generator_word_mem_pfil (hE : GlRel E) (a b : Fin n) (hab : ε a = ε b) (y : V) (hy : y ∈ kSpan ε E u) :
    ∀ w : List (Fin n × Fin n), (∀ p ∈ w, ε p.1 ≠ ε p.2) →
      E a b (ew E w y) ∈ pfil ε E u w.length := by sorry
