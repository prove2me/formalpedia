-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_card_fixed_ge
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_fixed_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:24.666928+00:00
-- url     : https://prove2.me/theorems/ae974142-b6aa-41f8-923d-6e3924a24179
-- title:
--   Galois Irreducibility: card fixed ge
-- statement:
--   The Galois Irreducibility construction uses the card fixed ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRLemmaP.lean#L21-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRLemmaP.lean#L21-L41

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_fixed_ge (β : Type) [Fintype β] [DecidableEq β] (hβ : 1 ≤ Fintype.card β) :
    (Fintype.card β).factorial ≤
      2 * ((univ : Finset (Equiv.Perm β)).filter (fun s => ∃ x, s x = x)).card := by sorry
