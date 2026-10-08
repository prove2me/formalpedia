-- Prove2me | Theorems.Thm_DantzigSelector_Oracle_corollary_A_3
-- name    : DantzigSelector.Oracle.corollary_A_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:49:45.025099+00:00
-- url     : https://prove2.me/theorems/62abc843-f186-49e9-9fe1-eac52c84fd50
-- title:
--   Corollary A.3 — constrained thresholding (with the $\ell_1$ constant its proof gives)
-- statement:
--   Let $X\in\mathbb R^{n\times p}$ with columns $X_1,\dots,X_p$, let $S\ge1$ with $3S\le p$, write $\delta=\delta_{2S}$, $\theta=\theta_{S,2S}$, and assume $\delta+\theta<1$. Let $\beta$ be $S$-sparse with
--   $$\|\beta\|_{\ell_2}<\lambda\,S^{1/2}$$
--   for some $\lambda>0$. Then there is a decomposition $\beta=\beta'+\beta''$ such that
--   $$\|\beta'\|_{\ell_2}\le\frac{1+\delta}{1-\delta-\theta}\|\beta\|_{\ell_2},\qquad \|\beta'\|_{\ell_1}\le 2\,\frac{1+\delta}{1-\delta-\theta}\,\frac{\|\beta\|_{\ell_2}^2}{\lambda},\qquad \|X^*X\beta''\|_{\ell_\infty}<\frac{1-\delta^2}{1-\delta-\theta}\,\lambda.$$
--
--   The piece $\beta''$ is invisible to the Dantzig constraint at level of order $\lambda$, while the piece $\beta'$ is controlled in $\ell_2$ and $\ell_1$. In the proof of Theorem 1.2 this splits the small coefficients of the true parameter so that a perturbation of the hard-thresholded parameter is feasible for the Dantzig program.
--
--   **Formalization Note** The paper prints the $\ell_1$ bound without the factor $2$. Its proof applies Corollary A.2 with the real number $\|\beta\|_{\ell_2}^2/\lambda^2$ in place of the integer sparsity level and drops the $\sqrt2$ of (6.10); applying Corollary A.2 with the integer $\lceil\|\beta\|_{\ell_2}^2/\lambda^2\rceil$ and keeping $\sqrt2$ gives the bound with the factor $2$, which is what is stated here. The $\ell_2$ and $\ell_\infty$ bounds are as printed. $\|X^*X\beta''\|_{\ell_\infty}<\cdot$ is stated coordinatewise, $|\sum_i X_{ij}(X\beta'')_i|<\cdot$ for every $j$. The hypothesis $\delta+\theta<1$ is the appendix's standing hypothesis (Lemma A.1); $3S\le p$ is the domain of $\theta_{S,2S}$.
-- source:
--   Candès & Tao, The Dantzig Selector: Statistical Estimation When p Is Much Larger than n, arXiv:math/0506081v3, p. 38, Corollary A.3 (l1 constant corrected per its proof, pp. 38-39)

import Mathlib
import Definitions.Def_CandesTao_Decoding_Norms
import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_DantzigSelector_Sparse_Model
import Definitions.Def_DantzigSelector_Oracle_Model

open CandesTao.Decoding DantzigSelector.Sparse

namespace DantzigSelector.Oracle

/-- Candès–Tao (2007), Corollary A.3 (constrained thresholding), p. 38, with `δ = δ_{2S}`,
`θ = θ_{S,2S}`, `δ + θ < 1`: an `S`-sparse `β` with `‖β‖_{ℓ2} < λ √S` splits as
`β = β' + β''` with `‖β'‖_{ℓ2} ≤ (1 + δ)/(1 − δ − θ) ‖β‖_{ℓ2}`,
`‖β'‖_{ℓ1} ≤ 2 (1 + δ)/(1 − δ − θ) ‖β‖²_{ℓ2}/λ` (the printed bound without the factor `2` is
not what the paper's proof gives; see the item's Formalization Note) and
`‖X^* X β''‖_{ℓ∞} < (1 − δ²)/(1 − δ − θ) λ`. -/
theorem corollary_A_3 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (S : ℕ) (hS : 1 ≤ S)
    (hSp : 3 * S ≤ p)
    (hδθ : restrictedIsometryConst X (2 * S) + restrictedOrthogonalityConst X S (2 * S) < 1)
    (β : Fin p → ℝ) (hβ : IsSparse β S) (lam : ℝ) (hlam : 0 < lam)
    (hβlam : l2Norm β < lam * Real.sqrt S) :
    ∃ β' β'' : Fin p → ℝ, β = β' + β'' ∧
      l2Norm β' ≤
        (1 + restrictedIsometryConst X (2 * S)) /
          (1 - restrictedIsometryConst X (2 * S) - restrictedOrthogonalityConst X S (2 * S)) *
            l2Norm β ∧
      l1Norm β' ≤
        2 * (1 + restrictedIsometryConst X (2 * S)) /
          (1 - restrictedIsometryConst X (2 * S) - restrictedOrthogonalityConst X S (2 * S)) *
            (l2Norm β ^ 2 / lam) ∧
      ∀ j : Fin p, |∑ i, X i j * (X.mulVec β'') i| <
        (1 - restrictedIsometryConst X (2 * S) ^ 2) /
          (1 - restrictedIsometryConst X (2 * S) - restrictedOrthogonalityConst X S (2 * S)) *
            lam := by sorry

end DantzigSelector.Oracle
