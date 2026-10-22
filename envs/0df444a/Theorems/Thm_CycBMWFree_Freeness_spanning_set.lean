-- Prove2me | Theorems.Thm_CycBMWFree_Freeness_spanning_set
-- name    : CycBMWFree.Freeness.spanning_set
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:02.051033+00:00
-- url     : https://prove2.me/theorems/e7a7cf8b-02d7-4c25-b3eb-b4af54b5644d
-- title:
--   §6, p. 45 — spanning family of rank-size
-- statement:
--   For any commutative ground ring $S$, any degree-$r$ cyclotomic BMW parameters $P$, and every $n$, there is a family $b$ of $N(r,n)=r^n(2n-1)!!$ elements whose $S$-linear span is all of $W_{n,S,r}$:
--   $$
--   \exists b:\{1,\ldots,N(r,n)\}\to W_{n,S,r},\qquad \operatorname{span}_S\{b_i\}=W_{n,S,r}.
--   $$
--   The family supplies the upper bound on the number of generators without an admissibility assumption. **Formalization Note** The source calls the family a set of the stated cardinality. An indexed family allows coincident images in degenerate rings, including the zero ring.
-- source:
--   Goodman & Hauschild Mosley, Cyclotomic BMW algebras II, arXiv:math/0612065v5, p. 45, §6, citing [10] Proposition 3.6

import Mathlib
import Definitions.Def_CycBMWFree_Freeness_Setting

noncomputable section
open scoped BigOperators

namespace CycBMWFree.Freeness
open QAlgorithms.Papers.Independent.Support21.P14

/-- The spanning family cited in §6, p. 45. -/
theorem spanning_set {S : Type*} [CommRing S] {r : ℕ}
    (P : GroundParameters S r) (n : ℕ) :
    ∃ b : Fin (rankN r n) → BMW P n,
      Submodule.span S (Set.range b) = ⊤ := by sorry

end CycBMWFree.Freeness
