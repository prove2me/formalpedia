-- Prove2me | Theorems.Thm_Disjunctive_GeneralDisjunctions_rational_valid_cut_has_dual_feasible_tableau
-- name    : Disjunctive.GeneralDisjunctions.rational_valid_cut_has_dual_feasible_tableau
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-18T10:34:30.085723+00:00
-- url     : https://prove2.me/theorems/4ca9e354-a695-40ef-b234-fb67777b86ee
-- title:
--   A valid mixed-integer inequality admits a violating dual-feasible tableau
-- statement:
--   Let
--   $$P=\{x\in\mathbb R^\iota:Ax=b,\ x\ge0\},\qquad P_I=P\cap\{x:x_j\in\mathbb Z\ (j\in N')\},$$
--   where the finite matrix and right-hand side are rational. Assume that $P_I$ is nonempty and the inequality
--   $$\varphi x\ge\varphi_0$$
--   is valid for $P_I$ but violated by some point of $P$.
--
--   Then there are a basic feasible solution $v$, a partition into basic and nonbasic indices $I,J$, and an equivalent simplex tableau
--   $$x_i=v_i-\sum_{j\in J}\bar a_{ij}x_j\quad(i\in I),\qquad v_J=0,$$
--   such that
--   $$\varphi v<\varphi_0,\qquad \varphi r^j\ge0\quad(j\in J),$$
--   where $r^j_j=1$, $r^j_i=-\bar a_{ij}$ for $i\in I$, and the other nonbasic coordinates of $r^j$ vanish.
--
--   This is the basis-selection step needed to reconstruct the standard intersection cut from the halfspace $\varphi x\le\varphi_0$. The nonnegative reduced costs ensure that each ray either meets its boundary at a positive parameter or is parallel to it. No full-row-rank assumption on $A$ is imposed; redundant equations are allowed.
-- source:
--   Basis-selection support for Balas–Kis, On the relationship between standard intersection cuts, lift-and-project cuts, and generalized intersection cuts, Mathematical Programming 160 (2016), Theorem 13, preprint pp. 22–23, https://real.mtak.hu/42010/7/EBalas%20-%20TKis%20On%20the%20relationship%20%20%20latex%2012%2011%2015-tks.pdf ; equivalently Balas, Disjunctive Programming (2018), §11.2, Theorem 11.2, p. 152. The basis is chosen optimal for the facet normal so that the nonnegative reciprocal-exit convention is respected.

import Definitions.Def_Disjunctive_GeneralDisjunctions_SIC

theorem Disjunctive.GeneralDisjunctions.rational_valid_cut_has_dual_feasible_tableau
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ) (hrat : Disjunctive.GeneralDisjunctions.IsRationalData A b)
    (Nprime : Finset ι) (phi : ι → ℝ) (phi0 : ℝ)
    (hne : (Disjunctive.GeneralDisjunctions.MixedIntegerSet A b Nprime).Nonempty)
    (hvalid : ∀ x ∈ Disjunctive.GeneralDisjunctions.MixedIntegerSet A b Nprime,
      phi0 ≤ dotProduct phi x)
    (hcutoff : ∃ v ∈ Disjunctive.GeneralDisjunctions.LPFeasible A b, dotProduct phi v < phi0) :
    ∃ (I J : Finset ι) (abar : ι → ι → ℝ) (v : ι → ℝ),
      Disjunctive.GeneralDisjunctions.IsBasicFeasibleSolution A b I J abar v ∧
      dotProduct phi v < phi0 ∧
      ∀ j ∈ J, 0 ≤ dotProduct phi (Disjunctive.GeneralDisjunctions.extremeRay I abar j) := by sorry
