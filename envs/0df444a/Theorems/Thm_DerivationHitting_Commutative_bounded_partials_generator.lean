-- Prove2me | Theorems.Thm_DerivationHitting_Commutative_bounded_partials_generator
-- name    : DerivationHitting.Commutative.bounded_partials_generator
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:10:56.850737+00:00
-- url     : https://prove2.me/theorems/ecd52ce5-2c9f-494f-a4ab-cbc53cfe4217
-- title:
--   Theorem 1.1 — The explicit bounded-partials generator
-- statement:
--   Let $F$ be any characteristic-zero field and let $n,r\in\mathbb N$. Set $B=nr^2+r$ and define, independently of the input polynomial,
--   $$
--    G_i(t)=\sum_{k=1}^{B}\frac{(-1)^{k-1}i^k}{k}t^k\in F[t]\qquad(1\le i\le n).
--   $$
--   Every coordinate has degree at most $B$ and also at most $2nr^2$. For every polynomial $f\in F[x_1,\ldots,x_n]$ whose ordinary derivative space $V_f$ has dimension at most $r$,
--   $$
--    f=0\quad\Longleftrightarrow\quad f(G_1(t),\ldots,G_n(t))=0\quad\text{in }F[t].
--   $$
--   This is the uniform explicit polynomial substitution of Theorem 1.1, with its displayed realization on the same page. The generator depends only on $n,r$, and not on the coefficients of $f$. No input degree, homogeneity, Waring-rank, or extra field restriction is imposed. For degree at most $d$, evaluating its coordinates at $0,1,\ldots,dB$ yields a finite hitting set of at most $dB+1$ points. For a sum of $s$ degree-$d$ powers of linear polynomials one may use $r=s(d+1)$, including $d=0$.
--
--   **Formalization Note** At $r=0$ the generator is zero and the derivative bound forces $f=0$. At $n=0$ the substitution acts on scalar polynomials. The finite hitting-set observation is a consequence described here, not an additional clause asserted by this Lean item.
--
--   Differences from the source:
--   - encoding: variables indexed by 1,…,n → variables indexed by Fin n, with integer parameter i.val+1; reason: this is a bijective reindexing and the first kernel is nonzero
--   - encoding: dimension of the span of all ordinary partial derivatives → cardinal Module.rank of the span of derivatives indexed by all finite sequences, including the empty sequence; reason: finite-dimensional cardinal rank is ordinary dimension, and no finrank default is used
--   - encoding: coordinate degree O(nr²), realized by the displayed sum through B=nr²+r → the displayed generator with degree at most B and at most 2nr² in each coordinate; reason: for n,r positive B≤2nr²; for r=0 all coordinates are zero, and for n=0 there are no coordinates
-- source:
--   Shubham Bhardwaj, Foram Lakhani, Partha Mukhopadhyay, Ramprasad Saptharishi, Pratik Shastri, Amit Sinhababu, STOC 2027 submission #577 (October 2026), p. 3, Theorem 1.1, its following paragraph and displayed generator; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/577.pdf

import Definitions.Def_DerivationHitting_Commutative_PolynomialData

namespace DerivationHitting.Commutative
theorem bounded_partials_generator {F : Type*} [Field F] [CharZero F] (n r : ℕ) :
    (∀ i : Fin n, (generator (F := F) n r i).natDegree ≤ cutoff n r ∧
      (generator (F := F) n r i).natDegree ≤ 2 * n * r ^ 2) ∧
    (∀ f : MvPolynomial (Fin n) F, hasBoundedPartials f r →
      (f = 0 ↔ polynomialSubstitution n r f = 0)) := by sorry
end DerivationHitting.Commutative
