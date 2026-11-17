-- Prove2me | Theorems.Thm_AggCG_Supplement_theorem_L_2
-- name    : AggCG.Supplement.theorem_L_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:35:51.665646+00:00
-- url     : https://prove2.me/theorems/923ea3e8-42be-411f-8444-e32871be71b1
-- title:
--   Theorem L.2 — three gradient-descent capacity lower bounds
-- statement:
--   For the normalized capped iteration-count loss on rational piecewise-quadratic, possibly discontinuous objectives, there are regular polynomial-description witness families that $1/4$-fat-shatter:
--
--   1. $\lfloor(H-2)/2\rfloor\lfloor\log_2k\rfloor$ two-dimensional objectives for a constant step size, each with $O(H+k)$ affine boundaries;
--   2. ${\lfloor H/2\rfloor\choose2}=\Omega(H^2)$ two-dimensional objectives for an $H$-entry learning-rate schedule, each with $O(H)$ boundaries;
--   3. $d\lfloor H/2\rfloor$ objectives in dimension $d+1$ for a tunable $d$-coordinate initialization and fixed step size.
--
--   All witnesses avoid every piece boundary through the horizon, and all rational descriptions have one uniform polynomial bit bound.
--
--   Differences from the source:
--   - encoding: piecewise-quadratic objectives with polynomial descriptions and $O(\cdot)$ boundary counts → explicit rational affine-boundary/quadratic-piece structures with uniform polynomial bounds on boundaries, pieces, and coefficient codes; reason: these bounds make the total explicit structure polynomial-size and render the asymptotic quantifiers uniformly
-- source:
--   Sharma, STOC 2027 submission (manuscript sha256 f7ea0248…), Theorem L.2, p.65, PDF p.66

import Mathlib
import Definitions.Def_AggCG_Supplement_PQObj

namespace AggCG.Supplement

/-- **Theorem L.2** (Three matching capacity lower bounds; Sharma, *Computational Complexity of Data-Driven
Configuration for Integer Programming, Clustering, and Learning Algorithms*, STOC 2027 submission
(manuscript sha256 f7ea0248…), p.65, PDF p.66). For piecewise-quadratic, possibly discontinuous
objectives and the normalized capped iteration-count loss `cost/H` of gradient descent, the following
families exist, with regular witnesses and rational descriptions of polynomial bit length (one polynomial
for all parameters), each description complete (`Covers`):
(i) for constant step size and `H ≥ 4`, `k ≥ 2`: `⌊(H − 2)/2⌋⌊log₂ k⌋` objectives in dimension `2`, each with
at most `C(H + k)` affine boundaries (one constant `C`), `1/4`-fat-shattered;
(ii) for an `H`-entry learning-rate schedule: `C(⌊H/2⌋, 2)` two-dimensional objectives, each with at most
`C(H + 1)` affine boundaries, `1/4`-fat-shattered, and `C(⌊H/2⌋, 2) ≥ c H²` for `H ≥ 4`;
(iii) for a tunable initialization of `d` coordinates and a fixed step size: `d⌊H/2⌋` objectives in
dimension `d + 1`, `1/4`-fat-shattered.

**Formalization Note** An instance is an objective with its initial point (in (iii) the tunable `d`
coordinates come from the parameter and the last, clock coordinate from the instance). Fat-shattering is
non-strict at margin `1/4`, and every witness parameter is regular on every instance of the family (its run
avoids every piece boundary through the horizon). The stopping threshold `ϑ` is part of each family. The
closing sentence of the theorem (matching the upper bounds of [Sha26]) compares with another paper and is
not a statement about these families. -/
theorem theorem_L_2 :
    (∃ (Cb cb e : ℕ), ∀ (H k : ℕ), 4 ≤ H → 2 ≤ k → ∃ (ϑ : ℝ)
      (fam : Fin ((H - 2) / 2 * Nat.log 2 k) → PQObj 2 × (Fin 2 → ℚ)), 0 < ϑ ∧
      (∀ i, (fam i).1.Covers ∧ (fam i).1.nb ≤ Cb * (H + k) ∧ (fam i).1.maxBits ≤ cb * (H + k + 1) ^ e ∧
        (fam i).1.pieces.length ≤ cb * (H + k + 1) ^ e ∧
        ∀ a, Nat.size ((fam i).2 a).num.natAbs + Nat.size ((fam i).2 a).den ≤ cb * (H + k + 1) ^ e) ∧
      ∃ r : Fin ((H - 2) / 2 * Nat.log 2 k) → ℝ, ∀ b : Fin ((H - 2) / 2 * Nat.log 2 k) → Bool,
        ∃ η : ℝ, 0 < η ∧
          (∀ i, GDRegular (fam i).1 (fun a => ((fam i).2 a : ℝ)) (fun _ => η) H) ∧
          ∀ i, 1 / 4 ≤ ((gdCost (fam i).1 (fun a => ((fam i).2 a : ℝ)) (fun _ => η) ϑ H : ℝ) / H - r i) *
            (if b i then 1 else -1)) ∧
    (∃ (Cb cb e : ℕ), ∀ H : ℕ, ∃ (ϑ : ℝ) (fam : Fin ((H / 2).choose 2) → PQObj 2 × (Fin 2 → ℚ)), 0 < ϑ ∧
      (∀ i, (fam i).1.Covers ∧ (fam i).1.nb ≤ Cb * (H + 1) ∧ (fam i).1.maxBits ≤ cb * (H + 1) ^ e ∧
        (fam i).1.pieces.length ≤ cb * (H + 1) ^ e ∧
        ∀ a, Nat.size ((fam i).2 a).num.natAbs + Nat.size ((fam i).2 a).den ≤ cb * (H + 1) ^ e) ∧
      ∃ r : Fin ((H / 2).choose 2) → ℝ, ∀ b : Fin ((H / 2).choose 2) → Bool,
        ∃ η : Fin H → ℝ, (∀ t, 0 < η t) ∧
          (∀ i, GDRegular (fam i).1 (fun a => ((fam i).2 a : ℝ))
            (fun t => if h : t < H then η ⟨t, h⟩ else 0) H) ∧
          ∀ i, 1 / 4 ≤ ((gdCost (fam i).1 (fun a => ((fam i).2 a : ℝ))
            (fun t => if h : t < H then η ⟨t, h⟩ else 0) ϑ H : ℝ) / H - r i) * (if b i then 1 else -1)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ H : ℕ, 4 ≤ H → c * (H : ℝ) ^ 2 ≤ ((H / 2).choose 2 : ℕ)) ∧
    (∃ (cb e : ℕ), ∀ (H d : ℕ), 1 ≤ d → ∃ (ϑ η : ℝ) (fam : Fin (d * (H / 2)) → PQObj (d + 1) × ℚ),
      0 < ϑ ∧ 0 < η ∧
      (∀ i, (fam i).1.Covers ∧ (fam i).1.nb ≤ cb * (H + d + 1) ^ e ∧
        (fam i).1.pieces.length ≤ cb * (H + d + 1) ^ e ∧
        (fam i).1.maxBits ≤ cb * (H + d + 1) ^ e ∧
        Nat.size (fam i).2.num.natAbs + Nat.size (fam i).2.den ≤ cb * (H + d + 1) ^ e) ∧
      ∃ r : Fin (d * (H / 2)) → ℝ, ∀ b : Fin (d * (H / 2)) → Bool,
        ∃ z : Fin d → ℝ,
          (∀ i, GDRegular (fam i).1 (Fin.lastCases ((fam i).2 : ℝ) z) (fun _ => η) H) ∧
          ∀ i, 1 / 4 ≤ ((gdCost (fam i).1 (Fin.lastCases ((fam i).2 : ℝ) z) (fun _ => η) ϑ H : ℝ) / H
            - r i) * (if b i then 1 else -1)) := by sorry

end AggCG.Supplement
