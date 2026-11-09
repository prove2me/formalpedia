-- Prove2me | Theorems.Thm_DerivationHitting_Commutative_trivial_constants
-- name    : DerivationHitting.Commutative.trivial_constants
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:19.693801+00:00
-- url     : https://prove2.me/theorems/7050697b-f1aa-4862-8d86-710d93673939
-- title:
--   Lemma 2.4 — The concrete derivation has trivial constants
-- statement:
--   Let $F$ be a characteristic-zero field and let $n\in\mathbb N$. On $R=F(t)[x_1,\ldots,x_n]$, set $D=\partial_t+\sum_{i=1}^n\frac{i}{1+it}\partial_{x_i}$. Its ring of constants is exactly $F$:
--   $$
--    \forall h\in R,\qquad Dh=0\quad\Longleftrightarrow\quad \exists c\in F,\ h=c.
--   $$
--   This supplies the trivial-constants hypothesis of Lemma 2.3 for the logarithmic kernels. It holds over an arbitrary characteristic-zero field; no algebraic closedness assumption is imposed.
--
--   Differences from the source:
--   - encoding: variables indexed by 1,…,n → variables indexed by Fin n, with integer parameter i.val+1; reason: this is a bijective reindexing and the first kernel is nonzero
--   - encoding: the ring of constants is trivial, that is ker D = F → both directions of Dh = 0 iff h is an embedded scalar; reason: this expands the exact ring equality rather than merely stating one inclusion
-- source:
--   Shubham Bhardwaj, Foram Lakhani, Partha Mukhopadhyay, Ramprasad Saptharishi, Pratik Shastri, Amit Sinhababu, STOC 2027 submission #577 (October 2026), p. 11, Lemma 2.4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/577.pdf

import Definitions.Def_DerivationHitting_Commutative_DifferentialData

namespace DerivationHitting.Commutative
theorem trivial_constants {F : Type*} [Field F] [CharZero F] (n : ℕ) :
    hasTrivialConstants (F := F) (n := n) logarithmKernel := by sorry
end DerivationHitting.Commutative
