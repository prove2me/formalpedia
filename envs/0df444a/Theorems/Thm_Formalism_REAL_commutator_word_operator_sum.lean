-- Prove2me | Theorems.Thm_Formalism_REAL_commutator_word_operator_sum
-- name    : Formalism.REAL.commutator_word_operator_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:19:57.799368+00:00
-- url     : https://prove2.me/theorems/fae14d55-3ee6-4c17-891e-a731b8b59c6b
-- title:
--   REAL: commutator word operator sum
-- statement:
--   The REAL construction uses the commutator word operator sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L464-L504
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L464-L504

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

theorem Formalism.REAL.commutator_word_operator_sum (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (c d : Fin n) :
    ∀ (j : ℕ) (α : Fin j → Fin n × Fin n), E c d * u1W E α - u1W E α * E c d =
      ∑ i, ((if d = (α i).1 then u1W E (Function.update α i (c, (α i).2)) else 0) -
        (if (α i).2 = c then u1W E (Function.update α i ((α i).1, d)) else 0)) := by sorry
