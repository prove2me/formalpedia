-- Prove2me | Theorems.Thm_CommThresholdPR_StrongConverse_proposition_2_5
-- name    : CommThresholdPR.StrongConverse.proposition_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:51.214309+00:00
-- url     : https://prove2.me/theorems/755a381b-117e-4f49-9c3e-369e514a61bf
-- title:
--   Proposition 2.5 — information cost is at most communication
-- statement:
--   For every finite binary interactive protocol $\pi$ and every joint input law $\nu$,
--   $$\operatorname{IC}_{\nu}(\pi)\le\operatorname{Cost}_{\rm wc}(\pi).$$
--   The information cost conditions on the independent public randomness. Arbitrary finite private randomness and arbitrary finite protocol depth are included. This compares operational communication with its information cost.
--
--   Differences from the source:
--   - encoding: finite public randomness and independent finite private random tapes → finite public seeds and private local kernels on finite binary trees; reason: finite contingent choice tables realize the kernels as independent private tapes; posterior local tape laws recover every source transcript/output law and cost without any uniform bound
-- source:
--   Daiki Suruga, The Exact Communication Threshold for Parallel Repetition, STOC 2027 submission #304 (October 2026), Proposition 2.5, p. 9, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/304.pdf

import Definitions.Def_CommThresholdPR_StrongConverse_Simulation

namespace CommThresholdPR.StrongConverse

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
theorem proposition_2_5 (ν : PMF (X × Y)) (π : Protocol X Y A B) :
    π.info ν ≤ (π.cost : ℝ) := by sorry

end CommThresholdPR.StrongConverse
