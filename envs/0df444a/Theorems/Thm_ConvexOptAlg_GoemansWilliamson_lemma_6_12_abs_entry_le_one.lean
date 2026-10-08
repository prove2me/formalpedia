-- Prove2me | Theorems.Thm_ConvexOptAlg_GoemansWilliamson_lemma_6_12_abs_entry_le_one
-- name    : ConvexOptAlg.GoemansWilliamson.lemma_6_12_abs_entry_le_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T19:21:39.671363+00:00
-- url     : https://prove2.me/theorems/3fd86324-8b09-47ff-a375-bf27912dcca0
-- title:
--   §6.6, proof of Lemma 6.12, p. 345 — a PSD matrix with unit diagonal has |Σ_ij| ≤ 1
-- statement:
--   Let $\Sigma\in\mathbb R^{n\times n}$ be symmetric positive semidefinite with $\Sigma_{i,i}=1$ for every $i\in[n]$. Then every entry satisfies
--
--   $$|\Sigma_{i,j}|\le 1\qquad\text{for all } i,j\in[n].$$
--
--   In particular every feasible point of the MAXCUT SDP relaxation has entries in $[-1,1]$, which is the range on which inequality (6.8) is applied in the proof of the Goemans–Williamson bound.
-- source:
--   Bubeck, arXiv:1405.4980v2, §6.6, proof of Lemma 6.12, p. 345 (remark in the second sentence)

import Mathlib
import Definitions.Def_ConvexOptAlg_GoemansWilliamson_Defs

namespace ConvexOptAlg.GoemansWilliamson

/-- Remark in the proof of Lemma 6.12 (Bubeck, arXiv:1405.4980v2, §6.6, p. 345): a positive
semidefinite matrix `Σ` with unit diagonal (`Σ i i = 1` for all `i`) has all entries bounded by
one in absolute value, `|Σ i j| ≤ 1`. -/
theorem lemma_6_12_abs_entry_le_one {n : ℕ} (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hpsd : Sig.PosSemidef) (hdiag : ∀ i, Sig i i = 1) (i j : Fin n) :
    |Sig i j| ≤ 1 := by sorry

end ConvexOptAlg.GoemansWilliamson
