-- Prove2me | Theorems.Thm_ConstRegretMatch_Acyclic_eq_4_basis_inverse
-- name    : ConstRegretMatch.Acyclic.eq_4_basis_inverse
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:36:31.800537+00:00
-- url     : https://prove2.me/theorems/f588c332-44e9-488a-99b1-b95d637d9afd
-- title:
--   §4.2, p. 20, (4) — under GP the basis matrix ℬ is invertible and (z*_{ℳ₊}, s*_{𝒬₊}) = ℬ⁻¹λ > 0
-- statement:
--   Let $(M, \lambda, r)$ be a matching network satisfying the general position condition, and let $(z^*, s^*)$ be the unique non-degenerate optimal solution of (SPP). Let $\mathcal B$ be the optimal basis matrix, whose columns are the columns of $M$ indexed by $\mathcal M_+$ and the unit vectors $e_j$ indexed by $j \in \mathcal Q_+$.
--
--   Then $\mathcal B$ is invertible: there is a matrix $Y$, with rows $y^l$ indexed by $l \in \mathcal M_+ \cup \mathcal Q_+$, such that $Y\mathcal B = I$ and $\mathcal B Y = I$. Moreover
--   $$\begin{bmatrix} z^*_{\mathcal M_+} \\ s^*_{\mathcal Q_+}\end{bmatrix} = \mathcal B^{-1}\lambda = Y\lambda,\qquad\text{i.e.}\qquad z^*_m = y^m\lambda > 0\ \ (m \in \mathcal M_+),\qquad s^*_j = y^j\lambda > 0\ \ (j \in \mathcal Q_+).$$
--
--   This representation of the optimal solution through the inverse of the basis holds for every network in general position; Theorem 5.1 identifies the rows $y^l$ explicitly in (SPP)-acyclic networks.
--
--   **Formalization Note** $Y$ is a two-sided inverse of $\mathcal B$ over the index types `Fin n` and $\mathcal M_+ \sqcup \mathcal Q_+$; no `Matrix.inv` (which is $0$ on singular matrices) is used, so the statement cannot be met by a junk inverse.
-- source:
--   Kerimov, Ashlagi, Gurvich, Dynamic Matching: Characterizing and Achieving Constant Regret, SSRN 3824407 (Sep 14, 2022), pp. 19–20, §4.2, display (4)

import Mathlib
import Definitions.Def_ConstRegretMatch_Acyclic_Network
import Definitions.Def_ConstRegretMatch_Acyclic_SPP

namespace ConstRegretMatch.Acyclic

/-- §4.2, p. 20, (4): under GP the optimal basis matrix `ℬ` (columns of `M` indexed by `ℳ₊`, unit
columns indexed by `𝒬₊`) has a two-sided inverse `Y = ℬ⁻¹`, and `Y` maps `λ` to the basic part of
the unique optimal solution: `z*_m = yᵐλ > 0` for `m ∈ ℳ₊` and `s*_j = yʲλ > 0` for `j ∈ 𝒬₊`. -/
theorem eq_4_basis_inverse {n d : ℕ} (N : MatchingNetwork n d) (r : Fin d → ℝ)
    (hr : ConstRegretMatch.Upper.IsMatchValues r) (lam : Fin n → ℝ) (hlam : ConstRegretMatch.Upper.IsArrivalRates lam)
    (z : Fin d → ℝ) (s : Fin n → ℝ) (hGP : IsGP N r lam z s) :
    ∃ Y : Matrix (ConstRegretMatch.Upper.BasisIdx z s) (Fin n) ℝ,
      Y * basisMatrix N z s = 1 ∧ basisMatrix N z s * Y = 1 ∧
      (∀ c, ConstRegretMatch.Upper.basicPart z s c = ∑ i, Y c i * lam i ∧ 0 < ∑ i, Y c i * lam i) := by sorry

end ConstRegretMatch.Acyclic
