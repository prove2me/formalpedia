-- Prove2me | Theorems.Thm_FairFacilityLoc_lemma_3_9
-- name    : FairFacilityLoc.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:13:24.59764+00:00
-- url     : https://prove2.me/theorems/40b14aeb-febe-40e8-abdc-b0a92f2f84c0
-- title:
--   Lemma 3.9 — the capacities bound the scores
-- statement:
--   Let $W$ be a finite family of nonnegative weight vectors with a vector of positive total mass, let $y$ be the output of the Score-Balanced mechanism over $W$ at a profile $\tilde x$, and let $y^*\neq y$ with $F_W(y^*)>0$. After the normalization of Step 1, every $a$ in the normalized family satisfies $Q_r(a)\le K_r$ in every coordinate $r$. Hence
--   $$\bar Q(a)\le\mathcal C\qquad\text{and}\qquad Q_{r^*}(a)\le K_{r^*}.$$
--
--   This is the point where the mechanism enters the analysis: it is the only property of the output that the later steps use.
--
--   Differences from the source:
--   - generalization: a linear group and the output of $M_d$ → a finite family of nonnegative weight vectors with a vector of positive mass, and the mechanism over it; reason: p.49 applies the lemma to such a family; linear groups are the vectors $w_j\mathbf 1_{G_j}$
--   - generalization: an optimal facility location $y^*$ → any $y^*\ne y$ with $F_W(y^*)>0$; reason: optimality is not used, and an optimum $y^*\ne y$ with positive value is such a point
--   - encoding: $d\le 3$ → $1\le d\le 3$; reason: dimensions are positive throughout the paper; (1.2) lists $1\le d\le3$
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Lemma 3.9, p.26 (PDF p.28); family form p.49 (PDF p.51)

import Mathlib
import Definitions.Def_FairFacilityLoc_scoreBalancedOver
import Definitions.Def_FairFacilityLoc_normalizePoint
import Definitions.Def_FairFacilityLoc_capacity

namespace FairFacilityLoc

/-- **Lemma 3.9** (Yan, Zhou, manuscript, sha256 642a1268…, p.26, PDF p.28), the link to the mechanism. Let `y` be the
output of the Score-Balanced mechanism over `W` on the profile `x̃`, and let `y* ≠ y` with `F_W(y*) > 0`. In the
normalized coordinates, every `a` satisfies `Q_r(a) ≤ K_r` in every coordinate `r`, hence `Q̄(a) ≤ C` and
`Q_{r*}(a) ≤ K_{r*}`.

**Formalization Note.** Stated for finite families of nonnegative weight vectors, as p.49 applies it. `y*` need not be
optimal: the proof uses only `y* ≠ y` and `F_W(y*) > 0`. -/
theorem lemma_3_9 {n d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) {W : Finset (Fin n → ℝ)}
    (hW : ∀ a ∈ W, ∀ i, 0 ≤ a i) (hpos : ∃ a ∈ W, 0 < mass a Finset.univ)
    (xt : Fin n → GeoSemialgCSP.E d) (ystar : GeoSemialgCSP.E d)
    (hne : ystar ≠ scoreBalancedOver d W xt) (hF : 0 < familyObjective xt W ystar) :
    let y := scoreBalancedOver d W xt
    let x : Fin n → GeoSemialgCSP.E d := fun i => normalizePoint y ystar (xt i)
    let z := normalizePoint y ystar ystar
    let W' := normalizeWeights xt W y ystar
    (∀ a ∈ W', ∀ r, posScore (penalty d) x a r ≤ capacity (penalty d) W' x r) ∧
      (∀ a ∈ W', weightedScore (penalty d) x z a ≤ weightedCapacity (penalty d) W' x z) ∧
      (∀ a ∈ W', ∀ r, IsTopCoord z r →
        posScore (penalty d) x a r ≤ capacity (penalty d) W' x r) := by sorry

end FairFacilityLoc
