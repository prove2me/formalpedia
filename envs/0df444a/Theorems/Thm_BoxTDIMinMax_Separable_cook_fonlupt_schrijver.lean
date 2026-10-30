-- Prove2me | Theorems.Thm_BoxTDIMinMax_Separable_cook_fonlupt_schrijver
-- name    : BoxTDIMinMax.Separable.cook_fonlupt_schrijver
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-30T00:08:47.173953+00:00
-- url     : https://prove2.me/theorems/93b690d7-5eaf-461d-b58d-79739a1c8170
-- title:
--   Cook–Fonlupt–Schrijver: a TDI system with integral matrix has an integral optimal dual solution with at most 2|S| positive components
-- statement:
--   Let $Q\in\mathbb Z^{I\times S}$ be an integral matrix and $b\in\mathbb Q^I$ a rational vector such that the system $Qx\ge b$ is totally dual integral (TDI). Let $c\in\mathbb Z^S$ be an integral cost vector for which the dual linear program
--
--   $$
--   \max\{\,yb \;:\; y\in\mathbb R^I,\ y\ge 0,\ yQ=c\,\}
--   $$
--
--   is feasible and has an objective value bounded from above (i.e. has a finite optimum). Then this maximum is attained by an **integral** optimal solution $y$ whose number of positive components is at most $2|S|$:
--
--   $$
--   \#\{\,i\in I : y(i)>0\,\}\le 2|S|.
--   $$
--
--   This is the sparsity theorem of Cook, Fonlupt and Schrijver (an integer analogue of Carathéodory's theorem) in the form used by Frank and Murota at the end of the proof of Theorem 3.3: combined with Proposition 2.1 (box-TDI implies TDI), it yields an optimal dual vector $y^*$ in the min-max formula (3.14) with at most $2|S|$ positive components. Cook, Fonlupt and Schrijver in fact obtain the bound $2|S|-1$ (and Sebő later $2|S|-2$); the weaker bound $2|S|$ stated here is the one Frank and Murota use.
--
--   **Formalization Note** TDI is the platform definition `IsTDI`: for every integral $c$ for which the real dual feasible set $\{y\ge0 : yQ=c\}$ is nonempty and the dual objective $yb$ is bounded above on it, there is an integral optimal $y$. The conclusion asks for an integral $y$ that is dual feasible, optimal among all real dual feasible vectors, and has at most $2|S|$ positive entries.
-- source:
--   Frank, Murota, A Discrete Convex Min-Max Formula for Box-TDI Polyhedra, arXiv:2007.03507v3, p. 15 (last paragraph of the proof of Theorem 3.3), citing W. Cook, J. Fonlupt, A. Schrijver, An integer analogue of Carathéodory's theorem, J. Combin. Theory Ser. B 40 (1986) 63–70, and A. Schrijver, Combinatorial Optimization (2003), Vol. A, Theorem 5.30

import Mathlib
import Definitions.Def_BoxTDIMinMax_Separable_Setting

namespace BoxTDIMinMax.Separable

open Matrix

/-- Cook–Fonlupt–Schrijver (1986), as used in the proof of Theorem 3.3, p. 15 of Frank–Murota:
if the system `Q x ≥ b` with integral `Q` is TDI and the integral cost `c` has a finite dual
optimum `max {y b : y ≥ 0, y Q = c}`, then this maximum is attained by an integral `y` with at most
`2|S|` positive components. -/
theorem cook_fonlupt_schrijver {ι S : Type*} [Fintype ι] [Fintype S]
    (Q : Matrix ι S ℤ) (b : ι → ℚ) (hTDI : IsTDI (ratMat Q) b) (c : S → ℤ)
    (hfeas : (DualFeas (ratMat Q) c).Nonempty)
    (hbdd : BddAbove (dualObj b '' DualFeas (ratMat Q) c)) :
    ∃ y : ι → ℤ, (fun i => (y i : ℝ)) ∈ DualFeas (ratMat Q) c ∧
      (∀ y' ∈ DualFeas (ratMat Q) c, dualObj b y' ≤ dualObj b (fun i => (y i : ℝ))) ∧
      (Finset.univ.filter (fun i => 0 < y i)).card ≤ 2 * Fintype.card S := by sorry

end BoxTDIMinMax.Separable
