-- Prove2me | Theorems.Thm_FairFacilityLoc_proposition_3_3
-- name    : FairFacilityLoc.proposition_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:16:12.919161+00:00
-- url     : https://prove2.me/theorems/49fa0a25-336a-4a60-a8a4-8350bd06ef2f
-- title:
--   Proposition 3.3 — $M_d$ is well defined, strategyproof, anonymous, coordinate-independent, unanimous
-- statement:
--   In every dimension, on sublinear group effects, the mechanism $M_d$ is well defined, strategyproof, anonymous, coordinate-independent and unanimous: $M_d(z,\dots,z;\mathcal G)=z$ for every $z\in\mathbb R^d$.
--
--   This holds for every choice of weight sets, and gives all the incentive properties of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: well defined → the IsLeast clause for the candidate set; reason: the output is written with sInf, and IsLeast says the printed minimum exists and is the output
--   - reading: the mechanism fixes a weight set $K_j$ of each $E_j$ → every WeightSelection (a weight set for each group of each group structure, no profile argument); reason: the choice changes the mechanism, and p.47 says the bound holds for every choice; this is the stronger reading
--   - encoding: in every dimension → $1\le d$; reason: dimensions are positive throughout the paper
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Proposition 3.3, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_FairFacilityLoc_IsStrategyproof
import Definitions.Def_FairFacilityLoc_scoreBalanced

namespace FairFacilityLoc

/-- **Proposition 3.3** (Yan, Zhou, manuscript, sha256 642a1268…, p.18, PDF p.20). In every dimension, on sublinear
group effects and for every choice of weight sets, `M_d` is well defined, strategyproof, anonymous,
coordinate-independent and unanimous.

**Formalization Note.** "Well defined" is the `IsLeast` clause for the candidate set of (2.4). -/
theorem proposition_3_3 (d : ℕ) (hd : 1 ≤ d) (K : WeightSelection) :
    (∀ {n m : ℕ} (G : GroupStructure n m) (x : Fin n → GeoSemialgCSP.E d) (r : Fin d),
      IsLeast (cutCandidates (fun _ S => IsWinning d K G S) x r) (scoreBalanced d K G x r)) ∧
      IsStrategyproof (scoreBalanced d K) ∧
      IsAnonymous (scoreBalanced d K) ∧
      IsCoordinateIndependent (scoreBalanced d K) ∧
      IsUnanimous (scoreBalanced d K) := by sorry

end FairFacilityLoc
