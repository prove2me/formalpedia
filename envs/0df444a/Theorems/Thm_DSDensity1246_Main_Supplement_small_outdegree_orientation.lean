-- Prove2me | Theorems.Thm_DSDensity1246_Main_Supplement_small_outdegree_orientation
-- name    : DSDensity1246.Main.Supplement.small_outdegree_orientation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:24:47.024205+00:00
-- url     : https://prove2.me/theorems/faf817ee-8824-4b21-a594-dc90f952013a
-- title:
--   Lemma A.1 — Small Outdegree Orientation
-- statement:
--   Let W⊆Yⁿ be any word class, with arbitrary Y, natural n≥0, and integer ℓ≥1. There is an ℓ-list orientation σ of its indexed one-inclusion hypergraph such that
--
--   $$\forall w\in W,\qquad \operatorname{outdeg}^{\ell}(w;\sigma)\le\left\lceil\mu_W^\ell(n)\right\rceil.$$
--
--   This supplies the infinite-label orientation needed for the realizable learner. There is no finiteness assumption on W or Y and no probability premise.
--
--   Differences from the source:
--   - encoding: maximum vertex outdegree in an arbitrary one-inclusion hypergraph → a pointwise bound for every vertex, counting finitely many Fin n directions and using the published nonnegative-real maximumDensity ceiling; reason: this preserves every bound for nonempty classes and interprets the empty maximum vacuously; n=0 has zero outdegree
-- source:
--   Chirag Pabbaraju, STOC 2027 submission #1246 (October 2026), p. 45, Lemma A.1; proof pp. 45-46

import Definitions.Def_DSDensity1246_Main_Supplement_orientation
import Definitions.Def_DSDensity1246_Main_maximumDensity

set_option autoImplicit false

namespace DSDensity1246.Main.Supplement

/-- Lemma A.1, p.45. No finiteness restriction, including n=0. -/
theorem small_outdegree_orientation {Y : Type*} (n ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (W : Set (Fin n → Y)) :
    ∃ σ : ListOrientation ℓ W, ∀ w : W,
      listOutdegree σ w ≤ ⌈maximumDensity ℓ W n⌉₊ := by sorry

end DSDensity1246.Main.Supplement
