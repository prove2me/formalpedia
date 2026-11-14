-- Prove2me | Theorems.Thm_BosonicLearn_fugacityFamily_occupation_split
-- name    : BosonicLearn.fugacityFamily_occupation_split
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T20:02:13.913004+00:00
-- url     : https://prove2.me/theorems/10fef88c-bc1f-4f11-91f0-9fbcef3883b5
-- title:
--   Occupation matrices of two far-apart members of the hard family: compressions $0\preceq B_-\preceq B_+$ with $\mathrm{Tr}(B_+-B_-)\gtrsim an\nu\xi$
-- statement:
--   The matrix-analytic part of the proof of Lemma 12.
--
--   Setting (§5.1): $1/n\le\nu\le1$, $0<\xi<1/32$, $R_X=r(1+\xi X)$ with $r=\frac{\nu}{(1-4\xi)(1+\nu)}$, for $X\in G_{\rm supp}$ (Hermitian, traceless, $\|X\|_{\rm op}\le4$). The photon occupation matrix is $N_X=R_X(1-R_X)^{-1}$.
--
--   There are absolute constants $c,C>0$ such that the following holds. Let $n\ge1$, $X_1,X_2\in G_{\rm supp}$ and $a>0$ with $\|X_2-X_1\|_{\rm tr}\ge a\,n$. Then, calling the two fugacity matrices $R_{X_1},R_{X_2}$ in a suitable order $(R_+,R_-)$, there exist a unitary $n\times n$ matrix $U$ and a set of modes $A\subseteq\{1,\dots,n\}$ such that the compressions
--
--   $$
--   B_\pm=P_A\,U\,N_\pm\,U^\dagger\,P_A,\qquad N_\pm=R_\pm(1-R_\pm)^{-1},
--   $$
--
--   ($P_A$ the coordinate projection on $A$) satisfy
--
--   $$
--   0\preceq B_-\preceq B_+\preceq C\,\mathbf 1,\qquad c\,a\,n\,\nu\,\xi\ \le\ \operatorname{Tr}(B_+-B_-)\ \le\ C\,|A|\,\nu\,\xi,
--   $$
--
--   $$
--   c\,|A|\,\nu\ \le\ \operatorname{Tr}B_-,\qquad\operatorname{Tr}(B_-+B_-^2)\ \le\ C\,|A|\,\nu .
--   $$
--
--   In the paper: $U$ diagonalizes $\Delta=N_{X_1}-N_{X_2}$, $A$ indexes the eigenvalues of the sign for which the positive part has trace at least $\|\Delta\|_{\rm tr}/2$ ($\Pi_+=U^\dagger P_AU$), $\delta_{\rm ph}=\operatorname{Tr}(B_+-B_-)=\operatorname{Tr}\Delta_+$, and the bounds are Eqs. (128), (129), (133), (134), (144), (145).
--
--   **Formalization Note** The paper's $\bar\nu=r/(1-r)$ is comparable to $\nu$, so the bounds are stated with $\nu$. $B_\pm$ are kept as $n\times n$ matrices supported on $A\times A$. The trace norm is `WHMultiplicativity.schattenNorm 1`, and $G_{\rm supp}$ is `Gsupp n`. The order $(R_+,R_-)$ is expressed by a disjunction of the two possibilities.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §5.7, proof of Lemma 12, Eqs. (124)–(134), (144)–(145)

import Mathlib
import Definitions.Def_BosonicLearn_fugacityFamily
import Definitions.Def_BosonicLearn_Gsupp

open scoped ENNReal Matrix ComplexOrder

namespace BosonicLearn

/-- **Occupation matrices of two far-apart members of the hard family (matrix-analytic part of Lemma 12).**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §5.7, proof of Lemma 12, Eqs. (124)–(134): the photon occupation matrix `N_X = R_X(I − R_X)^{−1}`, `Δ = N_{X₁} − N_{X₂}`,
the resolvent identity, `‖Δ‖_tr ≥ c ν̄ ξ ‖X₁ − X₂‖_tr`, `‖Δ‖_op ≤ C ν̄ ξ`, `c ν̄ I ≤ N_X ≤ C ν̄ I`, the projector `Π₊` onto the
positive part of `Δ`, and the compressions `B_± = Π₊ N Π₊` with `B₊ − B₋ = Δ₊ ≥ 0`, `δ_ph = Tr Δ₊`.

There are absolute constants `c, C > 0` such that for `n ≥ 1`, `1/n ≤ ν ≤ 1`, `0 < ξ < 1/32`, `X₁, X₂ ∈ G_supp` and
`a > 0` with `‖X₂ − X₁‖_tr ≥ a n`: after ordering the two fugacity matrices `R_{X₁}, R_{X₂}` suitably as `(R₊, R₋)`,
there are a unitary `U` (diagonalizing `N₊ − N₋`) and a set of modes `A` (its positive eigen-directions) such that
the compressions `B_± = P_A U N_± U† P_A` (`N_± = R_±(1 − R_±)⁻¹`) satisfy `0 ⪯ B₋ ⪯ B₊ ⪯ C·1`,

`c a n ν ξ ≤ Tr(B₊ − B₋) ≤ C |A| ν ξ`,  `c |A| ν ≤ Tr B₋`,  `Tr(B₋ + B₋²) ≤ C |A| ν`.

**Formalization Note.** `ν̄ = r/(1 − r)` of the paper is comparable to `ν` (`ν/2 ≤ ν̄ ≤ 4ν/3`·const), so the bounds are
stated with `ν`. `B_±` are `n × n` matrices supported on `A × A`. The trace norm is `WHMultiplicativity.schattenNorm 1`. -/
theorem fugacityFamily_occupation_split :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 1 ≤ n → ∀ ν : ℝ, 1 / (n : ℝ) ≤ ν → ν ≤ 1 → ∀ ξ : ℝ, 0 < ξ → ξ < 1 / 32 →
      ∀ X₁ ∈ Gsupp n, ∀ X₂ ∈ Gsupp n, ∀ a : ℝ, 0 < a →
        a * n ≤ WHMultiplicativity.schattenNorm 1 ((X₂ - X₁ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) →
        ∃ Rp Rm : Matrix (Fin n) (Fin n) ℂ,
          ((Rp = fugacityFamily ν ξ X₁ ∧ Rm = fugacityFamily ν ξ X₂) ∨
            (Rp = fugacityFamily ν ξ X₂ ∧ Rm = fugacityFamily ν ξ X₁)) ∧
          ∃ (U : Matrix (Fin n) (Fin n) ℂ) (A : Finset (Fin n)), Uᴴ * U = 1 ∧
            (Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) *
              Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0)).PosSemidef ∧
            (Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) * (U * (Rp * (1 - Rp)⁻¹) * Uᴴ) *
                Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) -
              Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) *
                Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0)).PosSemidef ∧
            (((C : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
              Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) * (U * (Rp * (1 - Rp)⁻¹) * Uᴴ) *
                Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0)).PosSemidef ∧
            c * a * n * ν * ξ ≤
              (Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) * (U * (Rp * (1 - Rp)⁻¹) * Uᴴ) *
                  Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) -
                Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) *
                  Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0)).trace.re ∧
            (Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) * (U * (Rp * (1 - Rp)⁻¹) * Uᴴ) *
                  Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) -
                Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) *
                  Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0)).trace.re ≤ C * A.card * ν * ξ ∧
            c * A.card * ν ≤
              (Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) *
                Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0)).trace.re ∧
            ((Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) *
                Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0)) +
              (Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) *
                Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0)) *
              (Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) *
                Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0))).trace.re ≤ C * A.card * ν := by sorry

end BosonicLearn
