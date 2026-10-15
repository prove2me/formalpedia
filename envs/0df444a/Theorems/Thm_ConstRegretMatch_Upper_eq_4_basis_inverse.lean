-- Prove2me | Theorems.Thm_ConstRegretMatch_Upper_eq_4_basis_inverse
-- name    : ConstRegretMatch.Upper.eq_4_basis_inverse
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:46.504319+00:00
-- url     : https://prove2.me/theorems/c125f656-c8ad-4eaf-8013-81c3a9fae33a
-- title:
--   §4.2, p. 20, (4) — under GP the basis ℬ is invertible, (z*_{ℳ₊}, s*_{𝒬₊}) = ℬ⁻¹λ > 0, and |Y_{ij}| ≤ ω
-- statement:
--   Fix the topology of a matching network. There is a constant $\omega>0$, depending only on the topology (on $n$ and $M$), with the following property. For every vector of match values $r>0$ and every arrival law $\lambda$ under which the network satisfies GP with optimal solution $(z^*,s^*)$, the optimal basis matrix $\mathcal B$ (columns of $M$ indexed by $\mathcal M_+$, unit columns indexed by $\mathcal Q_+$) has a two-sided inverse $Y=\mathcal B^{-1}$ such that
--   $$\begin{bmatrix} z^*_{\mathcal M_+}\\ s^*_{\mathcal Q_+}\end{bmatrix}=Y\lambda,$$
--   every basic value is positive, i.e.
--   $$z^*_m=y^m\lambda>0\ (m\in\mathcal M_+),\qquad s^*_j=y^j\lambda>0\ (j\in\mathcal Q_+), \tag{4}$$
--   where $y^m,y^j$ are the rows of $Y$, and every entry of $Y$ satisfies $|Y_{ij}|\le\omega$.
--
--   The representation $z^*_m=y^m\lambda$ is what the optimality test and the Lyapunov analysis use to compare a policy's realized match rates with the fluid optimum; the uniform bound $\omega$ is what makes their constants independent of $\lambda$.
--
--   **Formalization Note** The columns of $\mathcal B$ are indexed by the sum type $\mathcal M_+\oplus\mathcal Q_+$ instead of the paper's reordering "$\mathcal M_+=\{1,\dots,d-\varrho\}$". The statement asserts invertibility (the existence of $Y$ with $Y\mathcal B=I$ and $\mathcal BY=I$) rather than using a matrix inverse function, which would be $0$ on a singular matrix. The constant $\omega$ is quantified before $r$ and $\lambda$, as "$\omega$ depends on $n$ and $M$".
-- source:
--   Kerimov, Ashlagi, Gurvich, Dynamic Matching: Characterizing and Achieving Constant Regret, SSRN 3824407 (Sep 14, 2022), pp. 19–20, §4.2, (4)

import Mathlib
import Definitions.Def_ConstRegretMatch_Upper_Network
import Definitions.Def_ConstRegretMatch_Upper_SPP

namespace ConstRegretMatch.Upper

/-- §4.2, p. 20, (4): under GP the optimal basis matrix `ℬ` is invertible, its inverse `Y` maps
`λ` to the basic part of the optimal solution, `(z*_{ℳ₊}, s*_{𝒬₊}) = Yλ`, every basic value is
positive, and the entries of `Y` are bounded by a constant `ω > 0` that depends only on the
network (`n` and `M`), not on `r` or `λ`. -/
theorem eq_4_basis_inverse {n d : ℕ} (N : MatchingNetwork n d) :
    ∃ ω : ℝ, 0 < ω ∧
      ∀ (r : Fin d → ℝ), IsMatchValues r →
      ∀ (lam : Fin n → ℝ), IsArrivalRates lam →
      ∀ (z : Fin d → ℝ) (s : Fin n → ℝ), IsGP N r lam z s →
        ∃ Y : Matrix (BasisIdx z s) (Fin n) ℝ,
          Y * basisMatrix N z s = 1 ∧ basisMatrix N z s * Y = 1 ∧
          Y.mulVec lam = basicPart z s ∧
          (∀ c, 0 < basicPart z s c) ∧
          ∀ c i, |Y c i| ≤ ω := by sorry

end ConstRegretMatch.Upper
