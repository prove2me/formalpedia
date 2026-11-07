-- Prove2me | Theorems.Thm_CodeSW_lemma_30
-- name    : CodeSW.lemma_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:23:43.930354+00:00
-- url     : https://prove2.me/theorems/5c075a36-fa32-4d73-aaa6-f513978ecc55
-- title:
--   Lemma 30 — $\dim(\ker(A)\cap\mathrm{col}(B))=\dim\ker(AB)-\dim\ker(B)$
-- statement:
--   For matrices $A$ and $B$ for which the product $AB$ is defined,
--   $$\dim(\ker(A)\cap\mathrm{col}(B))=\dim(\ker(AB))-\dim(\ker(B)).$$
--   This identity computes the number of even covers supported on a given set of checks, which enters the dual coupling of Lemma 18.
--
--   Differences from the source:
--   - generalization: 'Let h, g be matrices' with a formula in A, B, used over F₂ → A ∈ K^{k×l}, B ∈ K^{l×j} over any field K; reason: the identity holds over any field and specializes to F₂
--   - encoding: dim ker(AB) − dim ker(B) → dim(ker A ∩ col B) + dim ker B = dim ker(AB); reason: this avoids natural-number subtraction, and ker B ⊆ ker AB makes the two forms equivalent
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), Lemma 30, p.36

import Mathlib
open Matrix

namespace CodeSW

/-- **Lemma 30.** For matrices `A` and `B` (with `AB` defined),
`dim(ker(A) ∩ col(B)) = dim(ker(AB)) − dim(ker(B))`
(Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*, arXiv:2510.08446, manuscript sha256
4e4abb5e…, Lemma 30, p.36).

**Formalization Note** The page says "Let h, g be matrices" but its formula is in `A, B`; it is
stated for `A ∈ K^{k×l}`, `B ∈ K^{l×j}` over any field `K` (the paper uses `K = F₂`). The
difference is written as a sum, `dim(ker A ∩ col B) + dim ker B = dim ker(AB)`, which avoids
natural-number subtraction (`ker B ⊆ ker AB`). -/
theorem lemma_30 {K : Type*} [Field K] {k l j : ℕ} (A : Matrix (Fin k) (Fin l) K)
    (B : Matrix (Fin l) (Fin j) K) :
    Module.finrank K ↥(LinearMap.ker A.mulVecLin ⊓ LinearMap.range B.mulVecLin) +
        Module.finrank K (LinearMap.ker B.mulVecLin) =
      Module.finrank K (LinearMap.ker (A * B).mulVecLin) := by sorry

end CodeSW
