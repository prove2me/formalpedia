-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_Supplement_partial_enumeration_signal
-- name    : ActiveLanguageGeneration.Hierarchy.Supplement.partial_enumeration_signal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:29:38.595501+00:00
-- url     : https://prove2.me/theorems/684c7d0a-b125-43da-961f-475093fa20ff
-- title:
--   Lemma B.4 — one correct output at time k gives active k-generation
-- statement:
--   Let $U$ be a countably infinite universe, $C$ a collection of infinite languages over $U$ and $k\ge1$. Suppose there is a map $G:U^k\to U$ such that every $L\in C$ has a partial enumeration $x_1,\ldots,x_k$ (distinct elements of $L$, in order) with
--
--   $$
--   G(x_1,\ldots,x_k)\in L\setminus\{x_1,\ldots,x_k\}.
--   $$
--
--   Then $C$ is actively $k$-generatable (with repetition). A single correct output at time $k$ therefore suffices for correctness at every later time.
--
--   Differences from the source:
--   - encoding: countably infinite universe U (without loss of generality N) → an arbitrary type U with [Countable U] [Infinite U]; reason: this is the paper's standing assumption of §2; every such U is in bijection with N
--   - encoding: a map G : U^k → U and a partial enumeration x1, …, xk → G : (Fin k → U) → U and an injective x : Fin k → U into L; reason: ordered k-tuples of distinct elements; same data
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Lemma B.4, printed p.27 (PDF p.28); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_ActiveKGeneratable

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- Lemma B.4, printed p.27 (PDF p.28): a map on `k`-tuples that is correct on some ordered
`k` distinct elements of every language yields an active `k`-generator (with repetition). -/
theorem partial_enumeration_signal (U : Type) [Countable U] [Infinite U]
    (C : LanguageCollection U) (k : ℕ) (hk : 0 < k)
    (h : ∃ G : (Fin k → U) → U, ∀ L ∈ C, ∃ x : Fin k → U, Function.Injective x ∧
      (∀ i, x i ∈ L.val) ∧ G x ∈ L.val \ Set.range x) :
    ActiveKGeneratable .R C k := by sorry

end ActiveLanguageGeneration.Hierarchy.Supplement
