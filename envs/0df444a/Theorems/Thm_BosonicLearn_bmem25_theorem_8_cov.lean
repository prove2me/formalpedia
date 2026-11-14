-- Prove2me | Theorems.Thm_BosonicLearn_bmem25_theorem_8_cov
-- name    : BosonicLearn.bmem25_theorem_8_cov
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-13T18:32:22.163093+00:00
-- url     : https://prove2.me/theorems/ec643753-6ab0-42bf-9338-92c4e6991fe4
-- title:
--   [BMEM25, Theorem 8], covariance part: $\tfrac12\|\rho(\mu,\Sigma')-\rho(\mu,\Sigma)\|_1\le\frac{1+\sqrt3}{8}\mathrm{Tr}[(\Sigma^{-1}+\Sigma'^{-1})(\Sigma'-\Sigma)]$ for $\Sigma'\succeq\Sigma$
-- statement:
--   A trace-distance bound for two Gaussian states with the same mean and ordered covariance matrices, without any gap above the vacuum.
--
--   Let $\rho(\mu,\Sigma)$ and $\rho(\mu,\Sigma')$ be $n$-mode Gaussian states with the same mean and $\Sigma'\succeq\Sigma$. Then
--
--   $$
--   \tfrac12\big\|\rho(\mu,\Sigma')-\rho(\mu,\Sigma)\big\|_1\;\le\;\frac{1+\sqrt3}{8}\;\operatorname{Tr}\!\Big[\big(\Sigma^{-1}+\Sigma'^{-1}\big)\big(\Sigma'-\Sigma\big)\Big].
--   $$
--
--   Source. This is the covariance part of Theorem 8 of Bittel, Mele, Eisert, Mele, *Energy-independent tomography of Gaussian states*, arXiv:2508.14979 ([BMEM25] in the paper): $\|\rho(V,t)-\rho(W,m)\|_1\le2\|V^{-1/2}(m-t)\|_2+\frac{1+\sqrt3}4\operatorname{Tr}((V^{-1}+W^{-1})|V-W|)$, specialized to equal means and $|V-W|=W-V$. The right-hand side is invariant under a common rescaling of the two covariance matrices, so it reads the same in the convention $V=2\Sigma$ of [BMEM25] (vacuum $V=\mathbf 1$) and in the convention of this mission (vacuum $\Sigma=\tfrac12\mathbf 1$).
--
--   Role. It is the trace-distance input of the gap-free heterodyne bound `BosonicLearn.bmem25_theorem_10` ($O(n^3/\epsilon^2)$ copies), used for $\nu<1/n$ in Corollary 19: with $\tilde\Sigma-\Sigma\preceq c\,\Sigma$ the right-hand side is at most $\frac{1+\sqrt3}{2}\,c\,n$, linear in $n$, where Theorem 7 of the paper gives $\sqrt n$ under a vacuum gap.
--
--   **Formalization Note** The states are given through `IsGaussianState`; the hypothesis is `Matrix.PosSemidef (S' − S)`; the bound is `ENNReal.ofReal` of the right-hand side with `Matrix.trace` and matrix inverses (covariance matrices of states are positive definite). The mean term of the cited theorem is not included; in the application it is handled by Lemma 18 of the paper.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.4, p. 10 (trace-distance bounds between Gaussian states [BMEM25]); proof of Corollary 19, p. 65 ([BMEM25, Theorem 10]); [BMEM25] = arXiv:2508.14979, Theorem 8

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_BosonicLearn_IsGaussianState

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **[BMEM25, Theorem 8], covariance part, for ordered covariances.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.4, p. 10: "an important foundation for these results is the recently developed set of bounds on the
trace distance between Gaussian states [BMM+25, Hol24, BMEM25, FRSF26]", and proof of Corollary 19, p. 65: "the
general heterodyne tomography bound of [BMEM25, Theorem 10] applies without using the vacuum-gap promise".
[BMEM25] = Bittel, Mele, Eisert, Mele, *Energy-independent tomography of Gaussian states*, arXiv:2508.14979,
Theorem 8: `‖ρ(V, t) − ρ(W, m)‖₁ ≤ 2‖V^{−1/2}(m − t)‖₂ + ((1 + √3)/4) Tr((V⁻¹ + W⁻¹)|V − W|)`.

For Gaussian states `ρ(µ, Σ′)` and `ρ(µ, Σ)` with the same mean and `Σ′ ⪰ Σ`,
`½‖ρ(µ, Σ′) − ρ(µ, Σ)‖₁ ≤ ((1 + √3)/8) · Tr((Σ⁻¹ + Σ′⁻¹)(Σ′ − Σ))`.

**Formalization Note.** Special case of the cited bound with equal means and `|Σ′ − Σ| = Σ′ − Σ`. The right-hand
side is invariant under a common rescaling of the covariances, so it is the same in the convention `V = 2Σ` of
[BMEM25] (vacuum `V = I`) and in the convention of this paper (vacuum `Σ = ½I`). Covariance matrices of
states are positive definite, so the inverses are the true inverses. -/
theorem bmem25_theorem_8_cov {n : ℕ} (ρ' ρ : State (Occupation (Fin n))) (μ : Fin n ⊕ Fin n → ℝ)
    (S' S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (h' : IsGaussianState ρ' μ S') (h : IsGaussianState ρ μ S) (hord : (S' - S).PosSemidef) :
    traceDist ρ'.coefficients ρ.coefficients ≤
      ENNReal.ofReal ((1 + Real.sqrt 3) / 8 * ((S⁻¹ + S'⁻¹) * (S' - S)).trace) := by sorry

end BosonicLearn
