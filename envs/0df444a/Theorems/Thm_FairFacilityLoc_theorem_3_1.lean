-- Prove2me | Theorems.Thm_FairFacilityLoc_theorem_3_1
-- name    : FairFacilityLoc.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:16:33.026197+00:00
-- url     : https://prove2.me/theorems/560e043d-41f2-4028-bd64-1c9fc9f016f9
-- title:
--   Theorem 3.1 — $M_d$ has ratio at most $\alpha_d$
-- statement:
--   The mechanism $M_d$ has approximation ratio at most $\alpha_d$ on sublinear group effects, where $\alpha_d=1+\sqrt d$ for $1\le d\le3$ and $\alpha_d=3$ for $d\ge4$:
--   $$\rho_{M_d}(d)\le\alpha_d.$$
--
--   This names the mechanism behind the goal theorem.
--
--   Differences from the source:
--   - reading: the mechanism fixes a weight set $K_j$ of each $E_j$ → every WeightSelection (a weight set for each group of each group structure, no profile argument); reason: the choice changes the mechanism, and p.47 says the bound holds for every choice; this is the stronger reading
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Theorem 3.1, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_FairFacilityLoc_ratio
import Definitions.Def_FairFacilityLoc_alpha
import Definitions.Def_FairFacilityLoc_scoreBalanced

namespace FairFacilityLoc

/-- **Theorem 3.1** (Yan, Zhou, manuscript, sha256 642a1268…, p.17, PDF p.19). `M_d` has approximation ratio at most `α_d` on
sublinear group effects, where `α_d = 1 + √d` for `1 ≤ d ≤ 3` and `α_d = 3` for `d ≥ 4`, for every choice of weight
sets. -/
theorem theorem_3_1 (d : ℕ) (hd : 1 ≤ d) (K : WeightSelection) :
    ratio (scoreBalanced d K) ≤ ENNReal.ofReal (alpha d) := by sorry

end FairFacilityLoc
