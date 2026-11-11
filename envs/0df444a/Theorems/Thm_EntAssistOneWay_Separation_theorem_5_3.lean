-- Prove2me | Theorems.Thm_EntAssistOneWay_Separation_theorem_5_3
-- name    : EntAssistOneWay.Separation.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:22.507051+00:00
-- url     : https://prove2.me/theorems/b0673e6f-9771-4640-a3c2-487e361f24bf
-- title:
--   Theorem 5.3 — a hard distribution for quantum protocols
-- statement:
--   Let $G,\zeta,D$ satisfy the standing assumptions and let $r\ge1$. There is a single probability law $\mu$ on shifted-equality inputs, chosen before the communication cost or moment exponent, such that every unassisted $C$-qubit strategy has average success at most
--   $$\tfrac12+2\,2^{C/p}\sqrt{p/2^r}+2^C\left((2^r-1)/D\right)^{1/p}\qquad(C\ge1,\ p\ge2\text{ even}).$$
--   The paper writes $1/2+O(\cdot)$; the proof on p. 36 gives coefficient two on the square-root term and one on the other term. This distributional estimate is uniform over all encoding states and all binary measurements, and underlies the public-coin lower bound.
--
--   Differences from the source:
--   - generalization: D is the least dimension of an irrep nontrivial on ζ → any integer D ≥ 1 for which all lower-dimensional representations kill ζ; reason: complete reducibility and unitarisability for finite groups give the source instance; the estimates use only this lower-dimensional vanishing
--   - generalization: a success bound written as 1/2 + O(·) → the displayed bound with coefficients two and one; reason: the p-th-root estimate on p. 36 applied to Theorem 5.8 supplies these explicit constants
--   - encoding: an input distribution and arbitrary unassisted C-qubit protocols → a finite probability mass and all QuantumStrategy encodings and effects; reason: private randomness and local ancillas are already represented by density matrices and POVMs; the distributional setting requires no public seed
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 26, Theorem 5.3; pp. 35–36, proof

import Definitions.Def_EntAssistOneWay_Separation_GroupProblems
import Definitions.Def_EntAssistOneWay_Separation_Probability

open scoped BigOperators ComplexOrder
open Classical
open BooleanHiddenPartition.LowerBounds
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- Theorem 5.3, p. 26, with the constants obtained on p. 36. -/
theorem theorem_5_3 (G : Type) [Group G] [Fintype G] (r : ℕ) (hr : 1 ≤ r)
    (ζ : G) (D : ℕ) (hζ : CentralThree ζ) (hD : DimensionGap ζ D) :
    ∃ μ : FiniteLaw (ShiftAlice G r × ShiftBob G r),
      ∀ C : ℕ, 1 ≤ C → ∀ p : ℕ, Even p → 2 ≤ p →
        ∀ P : QuantumStrategy (ShiftAlice G r) (ShiftBob G r) C,
          averageSuccess (shiftEq r) μ (quantumAccept P) ≤
            1 / 2 + 2 * Real.rpow 2 ((C : ℝ) / p) * Real.sqrt ((p : ℝ) / (2 : ℝ) ^ r) +
              (2 : ℝ) ^ C * Real.rpow (((2 : ℝ) ^ r - 1) / D) (1 / (p : ℝ)) := by sorry

end

end EntAssistOneWay.Separation
