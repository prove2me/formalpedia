-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_finite_active_hierarchy
-- name    : ActiveLanguageGeneration.Hierarchy.finite_active_hierarchy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T21:17:33.5649+00:00
-- url     : https://prove2.me/theorems/4f5b8078-e3cf-4c20-bd98-a025e1d2542a
-- title:
--   Theorem 4.1 — strict finite active-generation hierarchy
-- statement:
--   Let $U$ be a countably infinite universe. Write $\operatorname{Act}_{k,q}(C)$ for active generation of a collection $C$ after $k$ received examples under convention $q$, with $\mathrm R$ allowing repeated outputs and $\mathrm{NR}$ excluding every earlier output as well as received examples. Then
--
--   $$
--   \forall k\ge2\ \exists C_k\subseteq\{L\subseteq U:L\text{ infinite}\}:\quad
--   \operatorname{Act}_{k,\mathrm{NR}}(C_k)\ \land\ \neg\operatorname{Act}_{k-1,\mathrm R}(C_k).
--   $$
--
--   One generator succeeds from the kth example on a favorable full injective enumeration of every language in $C_k$. Conversely, every proposed lower-threshold generator has a language in this same collection for which every full injective enumeration has an incorrect output at some time at least $k-1$, even allowing repeated outputs. This gives the finite-level clause of the main hierarchy theorem.
--
--   Differences from the source:
--   - encoding: a countably infinite string universe, identified with positive integers without loss of generality in §2 → an arbitrary type U with Countable U and Infinite U; reason: these are exactly the standing universe conditions; a bijection transports histories, infinite languages, full enumerations and correctness, including the k-subset and tagged-union witness universes
--   - encoding: an arbitrary collection of infinite subsets of U → a set of the subtype Language U of infinite sets; reason: infinitude is carried by each language and no countability or effective-presentation assumption is imposed on the collection
--   - encoding: positive example times t and positive thresholds, with correctness at every t ≥ k → natural stream indices n with paper time n+1 and threshold test k ≤ n+1; positivity is explicit; reason: the kth example has index k−1; every earlier output remains excluded under NR and no correctness is evaluated on the empty history
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Theorem 4.1, printed p.18 (PDF p.19), proof printed pp.18–20 (PDF pp.19–21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_ActiveKGeneratable

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy

/-- Theorem 4.1, printed p.18 (PDF p.19), on an arbitrary countably infinite string universe. Both the NR upper bound and the R lower bound are retained. -/
theorem finite_active_hierarchy (U : Type) [Countable U] [Infinite U] :
    ∀ k : ℕ, 2 ≤ k → ∃ C : LanguageCollection U,
      ActiveKGeneratable .NR C k ∧ ¬ ActiveKGeneratable .R C (k - 1) := by sorry

end ActiveLanguageGeneration.Hierarchy
