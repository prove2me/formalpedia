-- Prove2me | Theorems.Thm_FairFacilityLoc_proposition_3_27
-- name    : FairFacilityLoc.proposition_3_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:12:43.41169+00:00
-- url     : https://prove2.me/theorems/623546fe-923f-4b99-81dc-f2fe2f782dd4
-- title:
--   Proposition 3.27 — the ratio for finite families of weight vectors
-- statement:
--   For $d\le3$ and every finite family of nonnegative weight vectors that contains a vector of positive total mass, the Score-Balanced mechanism over the family is well defined, the objective $F_W$ has a minimizer, and the output $y$ satisfies
--   $$F_W(y)\le(1+\sqrt d)F_W(y')$$
--   for every minimizer $y'$ of $F_W$.
--
--   The case of the vectors $w_j\mathbf 1_{G_j}$ is Proposition 3.4, the ratio for linear group effects.
--
--   Differences from the source:
--   - generalization: a finite family $K'\subseteq K$ → any finite family of nonnegative vectors with a vector of positive total mass; reason: the proof uses only these properties of the family, and $K'\subseteq K$ has them
--   - encoding: well defined → the IsLeast clause for the candidate set; reason: the output is written with sInf, and IsLeast says the printed minimum exists and is the output
--   - encoding: $d\le 3$ → $1\le d\le 3$; reason: dimensions are positive throughout the paper; (1.2) lists $1\le d\le3$
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Proposition 3.27, p.48 (PDF p.50)

import Mathlib
import Definitions.Def_FairFacilityLoc_scoreBalancedOver
import Definitions.Def_FairFacilityLoc_familyObjective

namespace FairFacilityLoc

/-- **Proposition 3.27** (Yan, Zhou, manuscript, sha256 642a1268…, p.48, PDF p.50). For `d ≤ 3` and every finite family of
weight vectors with a vector of positive total mass, the Score-Balanced mechanism over the family is well defined, the
objective `F_W` has a minimizer, and the output `y` satisfies `F_W(y) ≤ (1 + √d) F_W(y′)` for every minimizer `y′`.

**Formalization Note.** The printed `K′ ⊆ K` is replaced by "finite family of nonnegative vectors", which is all the
proof uses. Proposition 3.4 is the special case of the vectors `w_j 1_{G_j}`. -/
theorem proposition_3_27 {n d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) (W : Finset (Fin n → ℝ))
    (hW : ∀ a ∈ W, ∀ i, 0 ≤ a i) (hpos : ∃ a ∈ W, 0 < mass a Finset.univ) (x : Fin n → GeoSemialgCSP.E d) :
    (∀ r, IsLeast (cutCandidates (fun _ S => IsWinningOver d W S) x r) (scoreBalancedOver d W x r)) ∧
      (∃ y' : GeoSemialgCSP.E d, ∀ p, familyObjective x W y' ≤ familyObjective x W p) ∧
      (∀ y' : GeoSemialgCSP.E d, (∀ p, familyObjective x W y' ≤ familyObjective x W p) →
        familyObjective x W (scoreBalancedOver d W x) ≤
          (1 + √(d : ℝ)) * familyObjective x W y') := by sorry

end FairFacilityLoc
