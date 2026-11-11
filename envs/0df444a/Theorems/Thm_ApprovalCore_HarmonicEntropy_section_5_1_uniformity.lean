-- Prove2me | Theorems.Thm_ApprovalCore_HarmonicEntropy_section_5_1_uniformity
-- name    : ApprovalCore.HarmonicEntropy.section_5_1_uniformity
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:31:23.693736+00:00
-- url     : https://prove2.me/theorems/65b878ec-6520-43b7-ae09-f626aca34fae
-- title:
--   §5.1 — iterating $\Phi$ on a strictly positive $x$ more than $\max_j 1/x_j$ times gives a uniform vector
-- statement:
--   Let $x \in \Delta_d$ be strictly positive and let $M$ be an integer with $M > 1/x_j$ for every $j \in [d]$. Then applying $\Phi$ $M$ times to $x$ (the paper writes the result $\Phi^M(x)$) gives the uniform vector:
--   $$\underbrace{\Phi(\cdots\Phi}_{M}(x)\cdots) = \Big(\frac{1}{d+M}, \dots, \frac{1}{d+M}\Big) \in \Delta_{d+M}.$$
--   This is what makes the recursive definition of harmonic entropy well-founded: every strictly positive distribution becomes uniform after finitely many applications of $\Phi$.
--
--   Differences from the source:
--
--   - encoding: a distribution x ∈ ∆_d with coordinates indexed by [d] → x : Fin d → ℝ with x ∈ stdSimplex ℝ (Fin d), coordinates indexed 0, …, d−1; reason: Mathlib's standard simplex is exactly ∆_d (nonnegative coordinates summing to 1); only the index base changes
-- source:
--   Becker, Greger, Peters, Existence of the Core in Approval-Based Committee Elections, STOC 2027 submission (manuscript sha256 7cc237dc…), p. 9 (PDF 10), §5.1, paragraph 'Note that repeatedly applying Φ …'

import Mathlib
import Definitions.Def_ApprovalCore_HarmonicEntropy_RobinHood

namespace ApprovalCore.HarmonicEntropy

/-- §5.1 (p. 9): for a strictly positive `x ∈ ∆d` and an integer `M` strictly larger than
`1 / x_j` for every `j`, `M` applications of `Φ` give a uniform vector in `∆(d+M)` (the paper writes it `Φ^M(x)`). -/
theorem section_5_1_uniformity {d : ℕ} (x : Fin d → ℝ) (hx : x ∈ stdSimplex ℝ (Fin d))
    (hpos : StrictlyPositive x) (M : ℕ) (hM : ∀ j, 1 / x j < (M : ℝ)) :
    IsUniform (phiIter M x) := by sorry

end ApprovalCore.HarmonicEntropy
