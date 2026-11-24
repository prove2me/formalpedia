-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_card_stab_le
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_stab_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:12.696135+00:00
-- url     : https://prove2.me/theorems/e43d8b6c-6c2e-41ac-9f4c-998359a1a0ea
-- title:
--   Galois Irreducibility: card stab le
-- statement:
--   The Galois Irreducibility construction uses the card stab le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRLemmaP.lean#L62-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRLemmaP.lean#L62-L82

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {N : ℕ}

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_stab_le (A : Finset (Fin N)) :
    ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => ∀ x ∈ A, σ x ∈ A)).card ≤
      A.card.factorial * (N - A.card).factorial := by sorry
