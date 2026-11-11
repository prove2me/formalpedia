-- Prove2me | Theorems.Thm_ApprovalCore_HarmonicEntropy_lemma_5_1
-- name    : ApprovalCore.HarmonicEntropy.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:31:17.432739+00:00
-- url     : https://prove2.me/theorems/4f5507be-c17e-4c90-aa37-975cd463da9f
-- title:
--   Lemma 5.1 — the water level $t_\ell(x)$ as a maximum of averages (4) and as a minimum (5)
-- statement:
--   For every $x \in \Delta_d$ and integer $\ell \ge 0$, the water level $t_\ell(x) = \|\Phi^\ell(x)\|_\infty$ satisfies
--   $$t_\ell(x) = \max_{\emptyset \ne S \subseteq [d]} \frac{\sum_{j \in S} x_j}{|S| + \ell}, \qquad (4)$$
--   $$t_\ell(x) = \min\Big\{t \ge 0 : \sum_{j=1}^d (x_j - t)_+ \le \ell \cdot t\Big\}. \qquad (5)$$
--   Both maximum and minimum are attained. Formula (4) shows $t_\ell$ is a maximum of linear functions, hence continuous and convex, which is how concavity and continuity of $F$ are obtained.
--
--   **Formalization Note.** "Maximum" is `IsGreatest` of the set of values $\frac{\sum_{j\in S}x_j}{|S|+\ell}$ over non-empty `S : Finset (Fin d)`, and "minimum" is `IsLeast` of $\{t \ge 0 : \sum_j (x_j - t)_+ \le \ell t\}$; both say the extremum exists and equals $\|\Phi^\ell(x)\|_\infty$.
--
--   Differences from the source:
--
--   - encoding: a distribution x ∈ ∆_d with coordinates indexed by [d] → x : Fin d → ℝ with x ∈ stdSimplex ℝ (Fin d), coordinates indexed 0, …, d−1; reason: Mathlib's standard simplex is exactly ∆_d (nonnegative coordinates summing to 1); only the index base changes
--   - encoding: ∥y∥∞ → Mathlib's sup norm ‖y‖ on Fin d → ℝ; reason: the sup norm on a finite product of ℝ is max_j |y_j|, i.e. ∥y∥∞
-- source:
--   Becker, Greger, Peters, Existence of the Core in Approval-Based Committee Elections, STOC 2027 submission (manuscript sha256 7cc237dc…), p. 10 (PDF 11), Lemma 5.1, eqs. (4)–(5); proof p. 32 (PDF 33)

import Mathlib
import Definitions.Def_ApprovalCore_HarmonicEntropy_RobinHood

namespace ApprovalCore.HarmonicEntropy

/-- Lemma 5.1 (p. 10): for every `x ∈ ∆d` and integer `ℓ ≥ 0`, the water level
`tℓ(x) = ∥Φ^ℓ(x)∥∞` is the maximum (4) of `(∑_{j ∈ S} x_j) / (|S| + ℓ)` over non-empty
`S ⊆ [d]`, and the minimum (5) of `{t ≥ 0 : ∑_j (x_j − t)+ ≤ ℓ · t}`. -/
theorem lemma_5_1 {d : ℕ} (x : Fin d → ℝ) (hx : x ∈ stdSimplex ℝ (Fin d)) (ℓ : ℕ) :
    IsGreatest {v : ℝ | ∃ S : Finset (Fin d), S.Nonempty ∧
        v = (∑ j ∈ S, x j) / ((S.card : ℝ) + (ℓ : ℝ))} ‖robinHood ℓ x‖ ∧
      IsLeast {t : ℝ | 0 ≤ t ∧ ∑ j, posPart (x j - t) ≤ (ℓ : ℝ) * t} ‖robinHood ℓ x‖ := by sorry

end ApprovalCore.HarmonicEntropy
