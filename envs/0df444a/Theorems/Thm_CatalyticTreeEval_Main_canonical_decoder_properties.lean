-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_canonical_decoder_properties
-- name    : CatalyticTreeEval.Main.canonical_decoder_properties
-- status  : Proved
-- author  : @sragavan
-- created : 2026-11-14T02:18:17.276958+00:00
-- url     : https://prove2.me/theorems/39a53b43-fc0c-4260-bb4b-bf19cc2d1a04
-- title:
--   Explicit canonical-sumset decoder: full algebraic correctness
-- statement:
--   Let $p_1,\ldots,p_t$ be distinct odd primes and $m=\prod_i p_i$. The explicit decoder indexed by base-3 vectors has exactly $3^t$ terms. This theorem proves its cancellation and normalization, identifies the canonical sumset with residues whose projections all lie in $\{0,1,2\}$, and proves that the original canonical set is noncancelling. The decoder is the fixed construction in `Def_CatalyticTreeEval_DecoderCRT`; uniform native term access is a separate child.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Section 3.4, Lemma 3.19.

import Definitions.Def_CatalyticTreeEval_DecoderCRT

set_option autoImplicit false

namespace CatalyticTreeEval.Main

theorem canonical_decoder_properties {t : ℕ} (p : Fin t → ℕ) (hp : OddPrimeData p) :
    (∀ z : ZMod (modulus p), z ∈ sumset (canonical p (modulus p)) ↔
      ∀ i, z.val % p i = 0 ∨ z.val % p i = 1 ∨ z.val % p i = 2) ∧
    IsDecoder (sumset (canonical p (modulus p)))
      (DecoderConstruction.canonicalDecoder p hp.1) ∧
    Noncancelling (canonical p (modulus p)) := by sorry

end CatalyticTreeEval.Main
