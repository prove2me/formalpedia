-- Prove2me | Theorems.Thm_ContactTopology_positive_invariant_contact_representative_of_signed_dividing_data
-- name    : ContactTopology.positive_invariant_contact_representative_of_signed_dividing_data
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T21:14:17.796983+00:00
-- url     : https://prove2.me/theorems/85f89ca8-0ad9-4360-a91a-345aab744a2f
-- title:
--   Positive invariant contact representative from signed dividing data
-- statement:
--   Let $S\subset\mathbb R^2$ be compact, let $\beta=\beta_0\,dx+\beta_1\,dy$ be smooth, and let $r$ be a smooth signed function specifying the proposed dividing set and positive/negative regions. Set
--   $$w=(\beta_1,-\beta_0),\qquad h=\partial_x\beta_1-\partial_y\beta_0.$$
--   Suppose, on $S$, that $rh>0$ wherever $r\ne0$, and that the directed foliation crosses the proposed dividing set in the required direction:
--   $$dr(w)<0\qquad\text{where }r=0.$$
--
--   Then there is a globally smooth function $u$ with exactly the same zero set and sign as $r$, and an open neighborhood $O$ of $S$, such that
--   $$Q(u,\beta)=u h-du(w)>0\qquad\text{on }O.$$
--   Consequently $\alpha=\beta+u\,dz$ is an actual positive, vertically invariant contact form on $O\times\mathbb R$. Its central characteristic foliation is the one represented by $\beta$, and its normal coefficient vanishes exactly on the prescribed set. The function $u$ is constructed; its existence is not an input hypothesis.
--
--   These are the signed divergence and crossing conditions in the local normal-coefficient construction for divided foliations. When a directing field is given relative to a positive area density, multiplying it by that density yields the displayed Euclidean pair $w,h$ without changing the relevant signs.
--
--   The theorem assumes that a compatible global smooth signed function $r$ and the smooth planar coefficients $\beta$ have been supplied. It does not construct those data from an abstract embedded dividing multicurve, prove global contact positivity on the entire plane, or establish curved-chart transfer or the full Giroux flexibility theorem. It supplies the positive contact representative near the specified compact set from the explicit signed data.
-- source:
--   J. B. Etnyre, Convex Surfaces in Contact Geometry: Class Notes, https://etnyre.math.gatech.edu/preprints/papers/surfaces.pdf, Definition 2.13 and Theorem 2.15, printed pp.7–8, especially the normal-coefficient inequality (3). Signed-function planar formulation of the representative construction: a compatible smooth signed function is an explicit input; this does not claim its construction from arbitrary geometric dividing curves. A monotone clipped defining function yields the coefficient under the displayed signed divergence hypotheses.

import Mathlib
open scoped ContDiff

theorem ContactTopology.positive_invariant_contact_representative_of_signed_dividing_data
    (S : Set (Fin 2 → ℝ)) (hS : IsCompact S)
    (r : (Fin 2 → ℝ) → ℝ) (β : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (hr : ContDiff ℝ ∞ r) (hβ : ContDiff ℝ ∞ β)
    (hdiv : ∀ x ∈ S, r x ≠ 0 →
      0 < r x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0))
    (hcross : ∀ x ∈ S, r x = 0 → fderiv ℝ r x ![β x 1,-β x 0] < 0) :
    ∃ u : (Fin 2 → ℝ) → ℝ, ContDiff ℝ ∞ u ∧ (∀ x, u x = 0 ↔ r x = 0) ∧
      (∀ x, r x ≠ 0 → 0 < u x*r x) ∧
      ∃ O : Set (Fin 2 → ℝ), IsOpen O ∧ S ⊆ O ∧
        ∀ x ∈ O, 0 < β x 0*fderiv ℝ u x (Pi.single 1 1)-
          β x 1*fderiv ℝ u x (Pi.single 0 1)+
          u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0) := by sorry
