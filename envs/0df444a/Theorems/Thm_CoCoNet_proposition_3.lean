-- Prove2me | Theorems.Thm_CoCoNet_proposition_3
-- name    : CoCoNet.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:54.201695+00:00
-- url     : https://prove2.me/theorems/c42a0065-8a91-47a6-bc98-2229f30c9356
-- title:
--   Proposition 3 — fair case: $\Phi$ is continuous and surjective
-- statement:
--   Let $(m,W)$ be admissible, $l\ge0$, and let the thresholds be fair: $l_i=c_i/m_i$ for every bank. Then the map $\Phi$ is surjective and continuous. Consequently, for every asset vector $a\in\mathbb R^n$ there are a partition $(B,C,H)$ of $[n]$ and a price vector $s$ such that $(a,s)$ is a $(B,C,H)$-equilibrium.
--
--   This is existence of equilibrium in the fair case. Continuity fails as soon as one threshold is not fair, which is why the super-fair case (Theorem 1) needs a different argument.
--
--   Differences from the source:
--   - reading: no sign condition on the thresholds l stated → 0 ≤ l; reason: the paper asserts that the sets S_{B,C,H} partition ℝⁿ (p.12), which holds iff l ≥ 0; in the paper's setting lᵢ ≥ cᵢ/mᵢ with nonnegative debts cᵢ; without it the sets read off s overlap and Φ is not continuous
--   - encoding: banks [n] = {1, …, n}; vectors in ℝⁿ; matrix W = (w_ij) → banks Fin n (0-based); vectors Fin n → ℝ; W : Matrix (Fin n) (Fin n) ℝ with W i j = w_ij; reason: same objects, relabelled from 0
-- source:
--   Balter, Schweizer & Vera, Contingent Capital with Stock Price Triggers in Interbank Networks, arXiv:2011.06474v1, Proposition 3, p.17

import Mathlib
import Definitions.Def_CoCoNet_IsAdmissible
import Definitions.Def_CoCoNet_IsEquilibrium
import Definitions.Def_CoCoNet_Phi

namespace CoCoNet

/-- **Proposition 3 (fair case: Φ is continuous and surjective).**
Balter, Schweizer & Vera, arXiv:2011.06474v1, Proposition 3, p.17: "In the fair case with
lᵢ = cᵢ/mᵢ for all i ∈ [n], the mapping Φ is surjective and continuous. Thus, for every asset
value vector a ∈ ℝⁿ there exists a partition (B, C, H) of [n] and a stock price vector s such that
(a, s) is a (B, C, H)-equilibrium."

**Formalization Note.** `0 ≤ l` is a reading (in the fair case it is `c ≥ 0`, nonnegative debt);
without it the sets read off `s` do not partition `[n]` and `Φ` jumps at `sᵢ = 0`. -/
theorem proposition_3 {n : ℕ} (m : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (l c : Fin n → ℝ)
    (hadm : IsAdmissible m W) (hl : 0 ≤ l) (hfair : ∀ i, l i = c i / m i) :
    Function.Surjective (Phi m W l c) ∧ Continuous (Phi m W l c) ∧
      ∀ a : Fin n → ℝ, ∃ (B C H : Finset (Fin n)) (s : Fin n → ℝ),
        IsEquilibrium m W l c a s B C H := by sorry

end CoCoNet
