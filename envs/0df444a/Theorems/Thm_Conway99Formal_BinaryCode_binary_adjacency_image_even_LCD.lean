-- Prove2me | Theorems.Thm_Conway99Formal_BinaryCode_binary_adjacency_image_even_LCD
-- name    : Conway99Formal.BinaryCode.binary_adjacency_image_even_LCD
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T01:51:50.518597+00:00
-- url     : https://prove2.me/theorems/240b6a2f-9448-4456-a61e-1eec62bcc1bf
-- title:
--   The binary adjacency image is even and LCD
-- statement:
--   Let $G$ be a finite simple graph with strongly regular parameters $(99,14,1,2)$, and let $A_2$ be its actual adjacency matrix over $\mathbb{F}_2$. Then $A_2^2=A_2$, every word in the image of $A_2$ has even weight, and the image has trivial intersection with its orthogonal complement under the standard dot product. The image condition is stated as an actual preimage under $A_2$; no rank, minimum-distance, or graph-existence conclusion is assumed.
-- source:
--   Frozen formal source `formalization/2026-10-03/binary-code/BinaryCode.lean`, revision `a45708acebe3f397faccb1b646be906f24f23ee5`, raw SHA-256 `1437e9cd690e050f604a603b7826fef50f4ef1f6c0d21ef32c66c9793cb943e4`; source theorem `Conway99Formal.BinaryCode.solution`, jointly expressing adjacency idempotence, image evenness, and image LCD. The claim inventory is `formalization/2026-10-03/binary-code/claims.json` (raw SHA-256 `da91d6e8c4f067a8b875575bda42404b754b53f1457b366f61e08a7b565b3156`). The formal-algebra suite passed as run `run-d599319567b6` on revision `a45708acebe3f397faccb1b646be906f24f23ee5`; this records source QA, while the standalone candidate awaits coordinator compilation. Packaged standalone solution SHA-256 `6092b5f684039b9ed8f13d5ab4e36a3be966c9a29799cc2e7ae613d164500e78`.

import Mathlib
set_option autoImplicit false

theorem Conway99Formal.BinaryCode.binary_adjacency_image_even_LCD
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (G.adjMatrix (ZMod 2)) * (G.adjMatrix (ZMod 2)) = G.adjMatrix (ZMod 2) ∧
    (∀ x : V → ZMod 2,
      (G.adjMatrix (ZMod 2)).mulVec x ⬝ᵥ (G.adjMatrix (ZMod 2)).mulVec x = 0) ∧
    (∀ u : V → ZMod 2,
      (∃ x : V → ZMod 2, (G.adjMatrix (ZMod 2)).mulVec x = u) →
      (∀ y : V → ZMod 2, u ⬝ᵥ (G.adjMatrix (ZMod 2)).mulVec y = 0) → u = 0) := by sorry
