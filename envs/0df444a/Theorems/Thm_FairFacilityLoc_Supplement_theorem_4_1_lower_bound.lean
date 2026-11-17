-- Prove2me | Theorems.Thm_FairFacilityLoc_Supplement_theorem_4_1_lower_bound
-- name    : FairFacilityLoc.Supplement.theorem_4_1_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:29:12.040758+00:00
-- url     : https://prove2.me/theorems/d12c5d14-2070-4a0d-8cf6-7a12c6ccc367
-- title:
--   Theorem 4.1 — lower bound $\alpha_d$ on uniform group structures
-- statement:
--   Fix a positive dimension $d$. Every deterministic mechanism that is strategyproof and anonymous has approximation ratio at least
--
--   $$
--   \alpha_d=\begin{cases}
--   1+\sqrt d,&1\le d\le3,\\
--   3,&d\ge4,
--   \end{cases}
--   $$
--
--   even when the worst-case supremum is restricted to uniform group structures: disjoint equal-size groups partitioning the agents, with linear weight $1/K$ for every member of a size-$K$ group.
--
--   This is the paper’s matching lower bound. It applies to mechanisms that choose coordinates jointly and assumes neither coordinate independence nor continuity.
--
--   **Formalization Note** Determinism is built into the mechanism type. The restricted ratio is in $[0,\infty]$ with the paper’s zero-denominator conventions.
--
--   Differences from the source:
--   - encoding: every dimension $d$ → a natural number $d$ with $1\le d$ and locations in `EuclideanSpace ℝ (Fin d)`; reason: the paper works in positive finite-dimensional Euclidean space
--   - encoding: uniform linear groups with equal sizes and total masses, normalized on p.51 to weight $1/K$ → `IsUniform` requires the displayed normalized weight $1/K$; reason: this is the paper’s explicit normalization and common rescaling changes no ratio
--   - encoding: approximation ratio at least $\alpha_d$ on uniform structures → an inequality in $[0,\infty]$ against the restricted supremum `uniformRatio`; reason: it preserves the conventions $0/0=1$ and $a/0=\infty$
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Theorem 4.1, p.52 (PDF p.54)

import Mathlib
import Definitions.Def_FairFacilityLoc_IsStrategyproof
import Definitions.Def_FairFacilityLoc_alpha
import Definitions.Def_FairFacilityLoc_Supplement_uniformRatio

open scoped ENNReal

namespace FairFacilityLoc.Supplement

set_option autoImplicit false

/-- **Theorem 4.1 (Lower bound)** (Yan–Zhou, *Fair and Strategyproof Facility Location in
Euclidean Space*, manuscript, sha256 642a1268…, p.52, PDF p.54). Every deterministic,
strategyproof, anonymous mechanism has approximation ratio at least `α_d`, even when the
supremum is restricted to uniform group structures.

**Formalization Note.** Determinism is built into `FairFacilityLoc.Mechanism`. `uniformRatio`
uses the paper's normalization: disjoint equal-size groups partition the agents and every member
of a size-`K` group has weight `1/K`, so every group has total mass one. No coordinate
independence, continuity, unanimity, or finite-ratio hypothesis is imposed. -/
theorem theorem_4_1_lower_bound (d : ℕ) (hd : 1 ≤ d) (M : FairFacilityLoc.Mechanism d)
    (hsp : FairFacilityLoc.IsStrategyproof M) (han : FairFacilityLoc.IsAnonymous M) :
    ENNReal.ofReal (FairFacilityLoc.alpha d) ≤ uniformRatio M := by sorry

end FairFacilityLoc.Supplement
