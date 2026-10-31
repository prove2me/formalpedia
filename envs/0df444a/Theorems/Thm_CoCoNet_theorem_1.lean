-- Prove2me | Theorems.Thm_CoCoNet_theorem_1
-- name    : CoCoNet.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:12.680889+00:00
-- url     : https://prove2.me/theorems/e275b6f6-5239-4caa-b198-d54194358316
-- title:
--   Theorem 1 — with fair or super-fair thresholds an equilibrium exists for every asset vector
-- statement:
--   Let $(m,W)$ be an admissible network such that $I-W$ is invertible (Assumption 1). Let $l\ge0$ be the conversion thresholds and $c$ the credit amounts, and suppose every bank has set a fair or super-fair threshold:
--   $$l_i\ \ge\ \frac{c_i}{m_i}\qquad\text{for all } i\in[n].$$
--   Let $\hat\Phi$ be the map from stock prices to asset values for these credit amounts. Then
--   1. $\hat\Phi$ is surjective;
--   2. for every asset vector $a\in\mathbb R^n$ there is a price vector $s$ with $\hat\Phi(s)=a$ and a partition $(B,C,H)$ such that $(a,s)$ is a $(B,C,H)$-equilibrium.
--
--   In words: if no bank sets a sub-fair threshold, equilibrium stock prices exist for every realisation of asset values, although $\hat\Phi$ is in general neither continuous nor injective (equilibria may be multiple).
--
--   Differences from the source:
--   - reading: no sign condition on the thresholds l stated → 0 ≤ l; reason: the paper asserts that the sets S_{B,C,H} partition ℝⁿ (p.12), which holds iff l ≥ 0; in the paper's setting lᵢ ≥ cᵢ/mᵢ with nonnegative debts cᵢ; without it the sets read off s overlap and Φ is not continuous
--   - generalization: credit amounts cᵢ are convertible debts (implicitly cᵢ ≥ 0) → c : Fin n → ℝ of any sign; reason: the proof writes ĉ = m∘l − d with d ≥ 0 and never uses ĉ ≥ 0; nonnegative c is a special case
--   - encoding: the super-fair case Φ̂ with credit amounts ĉⱼ = cⱼ − dⱼ, dⱼ ≥ 0, cⱼ = mⱼlⱼ (fair or super-fair: lᵢ ≥ cᵢ/mᵢ) → Phi m W l c with ∀ i, c i / m i ≤ l i; reason: since mᵢ > 0 the two descriptions give the same maps; the fair case d = 0 is included, as in §3.3
--   - encoding: Assumption 1: I − W is invertible → IsUnit (1 - W); reason: the same condition for a square real matrix
--   - encoding: banks [n] = {1, …, n}; vectors in ℝⁿ; matrix W = (w_ij) → banks Fin n (0-based); vectors Fin n → ℝ; W : Matrix (Fin n) (Fin n) ℝ with W i j = w_ij; reason: same objects, relabelled from 0
-- source:
--   Balter, Schweizer & Vera, Contingent Capital with Stock Price Triggers in Interbank Networks, arXiv:2011.06474v1, Theorem 1, p.21; setting §3.3, p.18 ('l_i ≥ c_i/m_i for all i ∈ [n]', Assumption 1)

import Mathlib
import Definitions.Def_CoCoNet_IsAdmissible
import Definitions.Def_CoCoNet_IsEquilibrium
import Definitions.Def_CoCoNet_Phi

namespace CoCoNet

/-- **Theorem 1 (fair or super-fair thresholds: an equilibrium exists for every asset vector).**
Balter, Schweizer & Vera, arXiv:2011.06474v1, Theorem 1, p.21: "Under Assumption 1, the mapping Φ̂
associated with the super-fair case is surjective. Thus, for all vectors of asset values a ∈ ℝⁿ
there exists an associated vector of equilibrium stock prices s with Φ̂(s) = a."

The setting is §3.3, p.18: "all banks have set fair or super-fair thresholds, lᵢ ≥ cᵢ/mᵢ for all
i ∈ [n]", with Assumption 1: "The matrix I − W is invertible." `Φ̂ = Phi m W l c` for such credit
amounts `c`.

**Formalization Note.** Assumption 1 is `IsUnit (1 - W)`. `0 ≤ l` is a reading (the sets read
off `s` partition `[n]`, p.12; implied by `cᵢ ≥ 0` and `lᵢ ≥ cᵢ/mᵢ`). The credit amounts `c` are
not assumed nonnegative. -/
theorem theorem_1 {n : ℕ} (m : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (l c : Fin n → ℝ)
    (hadm : IsAdmissible m W) (hW : IsUnit (1 - W)) (hl : 0 ≤ l)
    (hsf : ∀ i, c i / m i ≤ l i) :
    Function.Surjective (Phi m W l c) ∧
      ∀ a : Fin n → ℝ, ∃ s : Fin n → ℝ, Phi m W l c s = a ∧
        ∃ B C H : Finset (Fin n), IsEquilibrium m W l c a s B C H := by sorry

end CoCoNet
