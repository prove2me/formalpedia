-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_Supplement_lemma_6_3
-- name    : FiniteGroupTesting.LinearQuery.Supplement.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:26:32.340198+00:00
-- url     : https://prove2.me/theorems/3cabde04-3591-4cae-a81f-248a2e72c0ee
-- title:
--   Lemma 6.3 — General common-exponent transcript coupling
-- statement:
--   There is a positive absolute constant $C$ such that the following holds for every nonempty finite family of distinct primes $p_i$ and positive ranks $a_i,b_i$. Let $H=\prod_i(\mathbb F_{p_i})^{a_i}$ and $K=\prod_i(\mathbb F_{p_i})^{b_i}$, of common exponent $P=\prod_i p_i$ and orders $m<n$, and put
--   $$\rho=(n-m)/n,\qquad\kappa=\min_i\{p_i^{a_i},p_i^{b_i}\}.$$
--   For every deterministic adaptive tree with at most $t\le m/10$ queries, the full transcripts under a uniform encoding of $K$ on $[n]$ and an independent uniform hidden copy of $H$ on an $m$-subset satisfy
--   $$d_{\rm TV}(\mathrm{Tr_Y},\mathrm{Tr_N})\le C\left(t\rho+t^2/\kappa\right).$$
--   The NO operation uses the fixed outside rule of the paper. The constant precedes primes, ranks, sizes and algorithm. This is the full product family, not a specialization to ranks $(3,2)$ and $(2,3)$, and it controls the entire joint transcript rather than only the final decision.
--
--   Differences from the source:
--   - encoding: labels [n]={1,...,n} → Fin n with zero representing paper label 1; reason: bijective relabelling preserves all tables, distances and query policies
--   - encoding: groups have common exponent equal to the product of their component primes → distinct primes and positive component dimensions in both groups, with additive coordinates Fin p_i; reason: these express exactly the displayed common-exponent family; an empty family cannot have m<n
--   - encoding: uniform subset followed by a uniform bijection, and all query-answer transcripts → uniform injections and their entire finite adaptive-tree transcripts, including a deterministic final bit; reason: these distributions are identical; the extra bit is a deterministic function of the transcript for the fixed tree, so total variation is unchanged
--   - reading: a random encoding of H on a random m-subset S, the lemma leaving the table outside S^2 unspecified → outside the image squared every product is label 0, which is paper label 1; reason: Section 6.1 (p. 35) fixes x*y := 1 outside S^2, and Theorem 6.1 applies the lemma with exactly this rule
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 35–36, Lemma 6.3

import Definitions.Def_FiniteGroupTesting_LinearQuery_Supplement_TranscriptModel

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery.Supplement

theorem lemma_6_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 0 < r → ∀ p a b : Fin r → ℕ,
      (∀ i, Nat.Prime (p i)) → Function.Injective p →
      (∀ i, 0 < a i) → (∀ i, 0 < b i) →
      let m := Fintype.card (Primary p a)
      let n := Fintype.card (Primary p b)
      m < n → ∀ t : ℕ, 10 * t ≤ m → ∀ T : QueryTree n t,
        transcriptTV T (encodingWeights (primaryAdd (p := p) (d := b)) n (zeroCompletion n))
          (encodingWeights (primaryAdd (p := p) (d := a)) n (zeroCompletion n)) ≤
            C * ((t : ℝ) * ((n : ℝ) - m) / n + (t : ℝ) ^ 2 / primaryMinimum p a b) := by sorry

end FiniteGroupTesting.LinearQuery.Supplement
