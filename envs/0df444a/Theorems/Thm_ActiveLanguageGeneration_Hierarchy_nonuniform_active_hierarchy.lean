-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_nonuniform_active_hierarchy
-- name    : ActiveLanguageGeneration.Hierarchy.nonuniform_active_hierarchy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-09T21:17:26.034817+00:00
-- url     : https://prove2.me/theorems/a3565dbf-865f-4dd9-adbe-224fbec0fe87
-- title:
--   Theorem 4.2 — active limit-generation beyond all finite levels
-- statement:
--   Let $U$ be a countably infinite universe. For a family $C$ of infinite languages, write $\operatorname{Act}_{\infty,\mathrm{NR}}(C)$ for the existence of one generator which, on a favorable full injective enumeration of each language, is correct without repeated outputs from some finite positive time onward. Write $\operatorname{Act}_{k,\mathrm R}(C)$ for active generation from the kth example with repeated outputs permitted. Then
--
--   $$
--   \exists C\subseteq\{L\subseteq U:L\text{ infinite}\}:\quad
--   \operatorname{Act}_{\infty,\mathrm{NR}}(C)\ \land\
--   \forall k\ge1,\ \neg\operatorname{Act}_{k,\mathrm R}(C).
--   $$
--
--   The single collection $C$ is chosen before all finite thresholds. Its positive result uses one generator for all its languages, although success times may depend on the language and its favorable enumeration. The negative result excludes every generator for every positive finite threshold, even under the more permissive repetition convention. This supplies the second clause of the main theorem.
--
--   Differences from the source:
--   - encoding: a countably infinite string universe, identified with positive integers without loss of generality in §2 → an arbitrary type U with Countable U and Infinite U; reason: these are exactly the standing universe conditions; a bijection transports histories, infinite languages, full enumerations and correctness, including the k-subset and tagged-union witness universes
--   - encoding: an arbitrary collection of infinite subsets of U → a set of the subtype Language U of infinite sets; reason: infinitude is carried by each language and no countability or effective-presentation assumption is imposed on the collection
--   - encoding: positive example times t and positive thresholds, with correctness at every t ≥ k → natural stream indices n with paper time n+1 and threshold test k ≤ n+1; positivity is explicit; reason: the kth example has index k−1; every earlier output remains excluded under NR and no correctness is evaluated on the empty history
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Theorem 4.2, printed p.20 (PDF p.21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_ActiveKGeneratable

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy

/-- Theorem 4.2, printed p.20 (PDF p.21): the same collection fails every finite
positive R threshold, while one generator succeeds eventually without repetition. -/
theorem nonuniform_active_hierarchy (U : Type) [Countable U] [Infinite U] :
    ∃ C : LanguageCollection U, ActiveLimitGeneratable .NR C ∧
      ∀ k : ℕ, 0 < k → ¬ ActiveKGeneratable .R C k := by sorry

end ActiveLanguageGeneration.Hierarchy
