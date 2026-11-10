-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_active_generation_hierarchy
-- name    : ActiveLanguageGeneration.Hierarchy.active_generation_hierarchy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T21:17:25.215665+00:00
-- url     : https://prove2.me/theorems/f9389e30-0caf-4c19-9600-5319ab287b85
-- title:
--   Theorem 1.2 — active generation hierarchy (both clauses)
-- statement:
--   Let $U$ be a countably infinite universe, and let collections consist of arbitrary families of infinite languages $L\subseteq U$. Write $\operatorname{Act}_{k,q}(C)$ for active generation from the kth received example, and $\operatorname{Act}_{\infty,q}(C)$ for active generation in the limit. The convention $q=\mathrm R$ permits repeated outputs; $q=\mathrm{NR}$ excludes every earlier output. Both conventions require outputs in the language and outside the examples received so far. The active generator is a single finite-history function for the collection and may use a favorable full injective presentation of each target language. The theorem asserts both:
--
--   $$
--   \begin{aligned}
--   &\forall k\ge2\ \exists C_k:\quad
--     \operatorname{Act}_{k,\mathrm{NR}}(C_k)\land\neg\operatorname{Act}_{k-1,\mathrm R}(C_k),\\
--   &\exists C:\quad \operatorname{Act}_{\infty,\mathrm{NR}}(C)\land
--     \forall k\ge1,\ \neg\operatorname{Act}_{k,\mathrm R}(C).
--   \end{aligned}
--   $$
--
--   Thus every finite level is strictly stronger than the preceding level, with the separation persisting across repetition conventions, and even the union of all finite levels misses an actively limit-generatable collection. The same $C$ witnesses every finite-threshold failure in the second clause. No countability assumption is placed on either collection. This is the full two-clause target of the mission.
--
--   Differences from the source:
--   - encoding: a countably infinite string universe, identified with positive integers without loss of generality in §2 → an arbitrary type U with Countable U and Infinite U; reason: these are exactly the standing universe conditions; a bijection transports histories, infinite languages, full enumerations and correctness, including the k-subset and tagged-union witness universes
--   - encoding: an arbitrary collection of infinite subsets of U → a set of the subtype Language U of infinite sets; reason: infinitude is carried by each language and no countability or effective-presentation assumption is imposed on the collection
--   - encoding: positive example times t and positive thresholds, with correctness at every t ≥ k → natural stream indices n with paper time n+1 and threshold test k ≤ n+1; positivity is explicit; reason: the kth example has index k−1; every earlier output remains excluded under NR and no correctness is evaluated on the empty history
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Theorem 1.2 (Active generation hierarchy), printed p.2 (PDF p.3); identified as the main theorem on printed p.22 (PDF p.23); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_ActiveKGeneratable

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy

/-- Theorem 1.2, both clauses, printed p.2 (PDF p.3).
All languages are infinite; collections need not be countable. The universe is arbitrary and countably infinite. No witness family or separation is assumed as a hypothesis. -/
theorem active_generation_hierarchy (U : Type) [Countable U] [Infinite U] :
    (∀ k : ℕ, 2 ≤ k → ∃ C : LanguageCollection U,
      ActiveKGeneratable .NR C k ∧ ¬ ActiveKGeneratable .R C (k - 1)) ∧
    (∃ C : LanguageCollection U, ActiveLimitGeneratable .NR C ∧
      ∀ k : ℕ, 0 < k → ¬ ActiveKGeneratable .R C k) := by sorry

end ActiveLanguageGeneration.Hierarchy
