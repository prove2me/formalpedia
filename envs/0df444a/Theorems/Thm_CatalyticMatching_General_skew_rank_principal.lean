-- Prove2me | Theorems.Thm_CatalyticMatching_General_skew_rank_principal
-- name    : CatalyticMatching.General.skew_rank_principal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:54:22.616546+00:00
-- url     : https://prove2.me/theorems/0d286444-4c5a-4430-9f52-628d865ebd05
-- title:
--   Fact 3.1 — even rank and largest nonsingular principal submatrix
-- statement:
--   Let $A$ be any rational skew-symmetric $n\times n$ matrix, with $n\ge0$. Then
--
--   $$\operatorname{rank}A\text{ is even},\qquad \operatorname{rank}A=\max\{|S|:\det A[S,S]\ne0\}.$$
--
--   The second assertion includes attainment and an upper bound for every nonsingular principal submatrix. The empty principal submatrix is included. This is the linear-algebraic foundation for the Tutte perturbation results.
--
--   Differences from the source:
--   - encoding: arbitrary finite labelled graph or matrix → vertices and indices in Fin n, with arbitrary n; reason: relabeling covers every finite instance, including n=0 and n=1
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, Fact 3.1, printed p.11 = PDF p.11

import Definitions.Def_CatalyticMatching_General_Tutte

namespace CatalyticMatching.General

/-- Fact 3.1 p.11, both clauses, over the standing field ℚ. Includes the empty principal submatrix. -/
theorem skew_rank_principal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : A.transpose = -A) :
    Even A.rank ∧
    (∃ S : Finset (Fin n), S.card = A.rank ∧
      (A.submatrix (fun i : S => i.val) (fun i : S => i.val)).det ≠ 0) ∧
    (∀ S : Finset (Fin n),
      (A.submatrix (fun i : S => i.val) (fun i : S => i.val)).det ≠ 0 → S.card ≤ A.rank) := by sorry

end CatalyticMatching.General
