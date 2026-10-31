-- Prove2me | Theorems.Thm_CoCoNet_Lmat_diag_dominant_isUnit
-- name    : CoCoNet.Lmat_diag_dominant_isUnit
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:34.282537+00:00
-- url     : https://prove2.me/theorems/8f121ca3-609c-440a-9f8a-0927ef39373f
-- title:
--   §2, pp.11–12 — the matrices $L_{B,C}$ are strictly diagonally dominant and invertible
-- statement:
--   Let $(m,W)$ be admissible. For all sets of banks $B,C\subseteq[n]$, the matrix $L_{B,C}=I+\mathrm{Diag}(m_B)+(I-W)\mathrm{Diag}(m_C)$ is strictly diagonally dominant by columns,
--   $$\sum_{i\ne j}\big|(L_{B,C})_{ij}\big|<\big|(L_{B,C})_{jj}\big|\qquad\text{for every } j,$$
--   and invertible.
--
--   For a partition $(B,C,H)$ the equilibrium equations read $a=L_{B,C}s+(I-W)c_H$; the page's closing remark, that $a$ is then determined by the partition and $s$, is part of Lemma 1. Invertibility is used throughout the analysis of $\Phi$ and in Lemma 5.
--
--   Differences from the source:
--   - reading: 'strictly diagonally dominant' (row or column not specified) → strict diagonal dominance by columns; reason: the paper's reason is the column-sum bound Σᵢ wᵢⱼ ≤ 1; row dominance fails in general (large mⱼ in a row)
--   - generalization: L_{B,C} for the blocks B, C of a partition → any B, C : Finset (Fin n), possibly overlapping; reason: Lemma 5 uses L_{B,C} for any B, C ⊆ [n]; partitions are a special case
--   - encoding: banks [n] = {1, …, n}; vectors in ℝⁿ; matrix W = (w_ij) → banks Fin n (0-based); vectors Fin n → ℝ; W : Matrix (Fin n) (Fin n) ℝ with W i j = w_ij; reason: same objects, relabelled from 0
-- source:
--   Balter, Schweizer & Vera, Contingent Capital with Stock Price Triggers in Interbank Networks, arXiv:2011.06474v1, §2, pp.11–12, after (3): 'the matrices L_{B,C} are strictly diagonally dominant and thus of full rank and invertible'

import Mathlib
import Definitions.Def_CoCoNet_IsAdmissible
import Definitions.Def_CoCoNet_Lmat

namespace CoCoNet

/-- **The matrices `L_{B,C}` are strictly diagonally dominant and invertible.**
Balter, Schweizer & Vera, arXiv:2011.06474v1, §2, pp.11–12, after (3): "Due to the fact that
Σ_{i∈[n]} wᵢⱼ ≤ 1 and mⱼ > 0, the matrices L_{B,C} are strictly diagonally dominant and thus of
full rank and invertible. This shows that for a given partition and a given s the vector a is
uniquely determined."

**Formalization Note.** Diagonal dominance is by columns (the hypothesis is on column sums of
`W`): `Σ_{i ≠ j} |(L_{B,C})ᵢⱼ| < |(L_{B,C})ⱼⱼ|`. Stated for all `B C : Finset (Fin n)`, possibly
overlapping, not only blocks of a partition. -/
theorem Lmat_diag_dominant_isUnit {n : ℕ} (m : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (hadm : IsAdmissible m W) (B C : Finset (Fin n)) :
    (∀ j, ∑ i ∈ Finset.univ.erase j, |Lmat m W B C i j| < |Lmat m W B C j j|) ∧
      IsUnit (Lmat m W B C) := by sorry

end CoCoNet
