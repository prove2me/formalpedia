-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_Supplement_finite_active_hierarchy_r
-- name    : ActiveLanguageGeneration.Hierarchy.Supplement.finite_active_hierarchy_r
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:31:07.133092+00:00
-- url     : https://prove2.me/theorems/11767c12-29eb-42da-819c-66009cfca2f3
-- title:
--   Theorem B.3 — strict finite active hierarchy with repetition
-- statement:
--   Let $U$ be a countably infinite universe. For every integer $k\ge2$ there is a collection $C_k$ of infinite languages over $U$ that is actively $k$-generatable with repetition but not actively $(k-1)$-generatable with repetition.
--
--   $$
--   \forall k\ge2\ \exists C_k:\quad C_k\in\mathrm{Act}^{k}_{\mathrm R}\setminus\mathrm{Act}^{k-1}_{\mathrm R}.
--   $$
--
--   It is the repetition-allowed version of the finite active hierarchy (Theorem 4.1).
--
--   Differences from the source:
--   - encoding: countably infinite universe U (without loss of generality N) → an arbitrary type U with [Countable U] [Infinite U]; reason: this is the paper's standing assumption of §2; every such U is in bijection with N
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Theorem B.3, printed p.27 (PDF p.28); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_ActiveKGeneratable

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- Theorem B.3, printed p.27 (PDF p.28), on a countably infinite universe. -/
theorem finite_active_hierarchy_r (U : Type) [Countable U] [Infinite U] :
    ∀ k : ℕ, 2 ≤ k → ∃ C : LanguageCollection U,
      ActiveKGeneratable .R C k ∧ ¬ ActiveKGeneratable .R C (k - 1) := by sorry

end ActiveLanguageGeneration.Hierarchy.Supplement
