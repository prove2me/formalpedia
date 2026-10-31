-- Prove2me | Theorems.Thm_CoCoNet_proposition_4
-- name    : CoCoNet.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:53.351116+00:00
-- url     : https://prove2.me/theorems/6b11033c-b483-45ba-8029-4405665afcb5
-- title:
--   Proposition 4 — fair case: $\Phi$ is a bijection, equilibrium is unique
-- statement:
--   Let $(m,W)$ be admissible, $l\ge0$, and $l_i=c_i/m_i$ for every bank (fair thresholds). Then $\Phi$ is injective, hence bijective, and for every asset vector $a$ there is exactly one pair (partition $(B,C,H)$, price vector $s$) such that $(a,s)$ is a $(B,C,H)$-equilibrium.
--
--   Bijectivity is what makes the fair healthy set $H(a)=\{i:\Phi^{-1}(a)_i>l_i\}$ of §3.3 well defined.
--
--   Differences from the source:
--   - reading: no sign condition on the thresholds l stated → 0 ≤ l; reason: the paper asserts that the sets S_{B,C,H} partition ℝⁿ (p.12), which holds iff l ≥ 0; in the paper's setting lᵢ ≥ cᵢ/mᵢ with nonnegative debts cᵢ; without it the sets read off s overlap and Φ is not continuous
--   - encoding: 'there exists a unique partition (B, C, H) of [n] and a stock price vector s' → ∃! of the pair ((B, C, H), s); reason: uniqueness of the pair, as printed
--   - encoding: banks [n] = {1, …, n}; vectors in ℝⁿ; matrix W = (w_ij) → banks Fin n (0-based); vectors Fin n → ℝ; W : Matrix (Fin n) (Fin n) ℝ with W i j = w_ij; reason: same objects, relabelled from 0
-- source:
--   Balter, Schweizer & Vera, Contingent Capital with Stock Price Triggers in Interbank Networks, arXiv:2011.06474v1, Proposition 4, p.18

import Mathlib
import Definitions.Def_CoCoNet_IsAdmissible
import Definitions.Def_CoCoNet_IsEquilibrium
import Definitions.Def_CoCoNet_Phi

namespace CoCoNet

/-- **Proposition 4 (fair case: Φ is a bijection; equilibrium exists and is unique).**
Balter, Schweizer & Vera, arXiv:2011.06474v1, Proposition 4, p.18: "In the fair case with
lᵢ = cᵢ/mᵢ for all i ∈ [n], the mapping Φ is injective, and thus also bijective. Thus, for every
asset value vector a there exists a unique partition (B, C, H) of [n] and a stock price vector s
such that (a, s) is a (B, C, H)-equilibrium."

The last conjunct asserts uniqueness of the pair (partition, price vector).

**Formalization Note.** `0 ≤ l` is a reading (as in Proposition 3). -/
theorem proposition_4 {n : ℕ} (m : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (l c : Fin n → ℝ)
    (hadm : IsAdmissible m W) (hl : 0 ≤ l) (hfair : ∀ i, l i = c i / m i) :
    Function.Injective (Phi m W l c) ∧ Function.Bijective (Phi m W l c) ∧
      ∀ a : Fin n → ℝ,
        ∃! P : (Finset (Fin n) × Finset (Fin n) × Finset (Fin n)) × (Fin n → ℝ),
          IsEquilibrium m W l c a P.2 P.1.1 P.1.2.1 P.1.2.2 := by sorry

end CoCoNet
