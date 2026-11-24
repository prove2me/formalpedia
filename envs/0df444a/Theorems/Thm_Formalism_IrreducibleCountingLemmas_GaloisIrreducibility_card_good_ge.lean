-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_card_good_ge
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_good_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:21.932933+00:00
-- url     : https://prove2.me/theorems/b93787bf-5161-4617-86d3-75a6292cc4af
-- title:
--   Galois Irreducibility: card good ge
-- statement:
--   The Galois Irreducibility construction uses the card good ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRLemmaP.lean#L84-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRLemmaP.lean#L84-L129

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_good_ge (A : Finset (Fin N)) (h1 : 1 ≤ A.card) (h2 : 1 ≤ N - A.card) :
    A.card.factorial * (N - A.card).factorial ≤
      4 * ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∀ x ∈ A, σ x ∈ A) ∧
        (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card := by sorry
