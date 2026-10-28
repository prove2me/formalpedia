-- Prove2me | Theorems.Thm_APrioriTSP_Sampling_proposition_12
-- name    : APrioriTSP.Sampling.proposition_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:34.625013+00:00
-- url     : https://prove2.me/theorems/2ab685bb-b1d2-4ff6-a0a8-c3eb628bd1f0
-- title:
--   Proposition 12, p. 10 — buckets of a sequence satisfying the triangle inequality satisfy B_{i+j} ≤ B_i + B_j
-- statement:
--   Let $b$ be odd and let $(C_j)_{j\ge1}$ be real numbers with $C_{i+j} \le C_i + C_j$ for all $i, j \ge 1$ (constraint (7)). Define the buckets
--   $$B_i = \sum_{j=\max\{1,\, ib - (b-1)/2\}}^{ib + (b-1)/2} C_j \qquad (i \ge 0).$$
--   Then for all $i, j \ge 1$,
--   $$B_{i+j} \le B_i + B_j .$$
--
--   The buckets aggregate $b$ consecutive hop sums around $ib$; the proposition says that this aggregation keeps the triangle inequality, which becomes constraint (14) of (Sampling-LP).
--
--   Differences from the source:
--
--   - generalization: the buckets of a feasible solution C of (Sampling-OP) → the buckets of any real sequence C satisfying (7); reason: the proof uses only (7); feasible solutions satisfy (7)
--   - encoding: an odd integer b ≥ b_0 for the constant b_0 > 0 of §2 (p. 7) → every odd natural number b; reason: b_0 is an arbitrary positive constant, so every odd b ≥ 1 qualifies with b_0 := b
-- source:
--   Blauth, Neuwohner, Puhlmann & Vygen, Improved guarantees for the a priori TSP, arXiv:2309.10663v1, p. 10, Proposition 12 and Equation (9)

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting
import Definitions.Def_APrioriTSP_Sampling_LP

namespace APrioriTSP.Sampling

/-- Proposition 12 (p. 10): buckets of odd size `b` of a sequence satisfying the triangle
inequality (7) satisfy `B_{i+j} ≤ B_i + B_j` for all `i, j ≥ 1`. -/
theorem proposition_12 (b : ℕ) (hb : Odd b) (C : ℕ → ℝ)
    (hC : ∀ i j, 1 ≤ i → 1 ≤ j → C (i + j) ≤ C i + C j) :
    ∀ i j, 1 ≤ i → 1 ≤ j → bucket b C (i + j) ≤ bucket b C i + bucket b C j := by sorry

end APrioriTSP.Sampling
