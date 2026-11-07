-- Prove2me | Theorems.Thm_ChoresEFX_algorithm_1_correct
-- name    : ChoresEFX.algorithm_1_correct
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:13:02.895115+00:00
-- url     : https://prove2.me/theorems/79f663f2-2043-4b48-9925-297844d3ef20
-- title:
--   Proof of Theorem 1.1, pp.19–20 — Algorithm 1 has a run and every output is $(3+\varepsilon)$-EFX for the original costs
-- statement:
--   For every well-formed instance and rational $0<\varepsilon\le1$, Algorithm 1 has a run, and every output $\sigma$ of every run is $(3+\varepsilon)$-EFX for the original costs.
--
--   This is the approximation half of Theorem 1.1; the machine and the time bound are the other half.
--
--   Differences from the source:
--   - reading: the proof shows the algorithm returns a (3 + ε)-EFX allocation → a run exists, and every run has the guarantee; reason: the strongest reading of an algorithm with free choices (paper.md decision 8)
--   - generalization: n ≥ 2 (standing, p.5) → n ≥ 1, with the single-agent case of §1.2 added to the run relation; reason: the proof says the case n = 1 is immediate, and the statement specializes to n ≥ 2
--   - encoding: dummy chores and a perfect matching in SSR → admissible matchings without dummies; reason: equivalent over all dummy placements (paper.md decision 9)
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), Proof of Theorem 1.1 and Corollary 1.2, pp.19–20

import Mathlib
import Definitions.Def_ChoresEFX_Alg1Run

namespace ChoresEFX

/-- **Correctness of Algorithm 1**, proof of Theorem 1.1 and Corollary 1.2, pp.19–20.

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC 2027
submission (manuscript sha256 b26d14cf…).

For every well-formed instance and rational `0 < ε ≤ 1`, Algorithm 1 has a run, and every output is `(3 + ε)`-EFX
for the original costs.

**Formalization Note.** This is the approximation half of Theorem 1.1; the goal adds the machine. -/
theorem algorithm_1_correct (I : Inst) (ε : ℚ) (hI : I.WellFormed) (hε : 0 < ε) (hε' : ε ≤ 1) :
    (∃ σ, Alg1Run I ε σ) ∧
    ∀ σ, Alg1Run I ε σ → IsAlphaEFX I.realCost (3 + (ε : ℝ)) σ := by sorry

end ChoresEFX
