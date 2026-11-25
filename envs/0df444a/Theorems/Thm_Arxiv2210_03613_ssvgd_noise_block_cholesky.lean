-- Prove2me | Theorems.Thm_Arxiv2210_03613_ssvgd_noise_block_cholesky
-- name    : Arxiv2210_03613.ssvgd_noise_block_cholesky
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T16:39:56.662981+00:00
-- url     : https://prove2.me/theorems/fe5ec4c3-be78-59d3-a37d-05c27c786150
-- title:
--   Eqs. (25)-(27): the sSVGD noise from the Cholesky factor of the $n\times n$ kernel matrix
-- statement:
--   Let $n\ge1$ particles $m_1,\dots,m_n\in\mathbb{R}^d$ and a function $k$ be such that $\overline K=[k(m_i,m_j)]_{i,j}$ is positive definite, and let $\overline L$ be the lower triangular Cholesky factor of $\overline K$. Let $K$ be the matrix of eq. (22), $D_K$ the matrix of eq. (25), $P$ the permutation (26), and $\epsilon_t>0$. Then:
--
--   1. $D_K=PKP^\top$.
--   2. The lower triangular Cholesky factor of $D_K$, for the coordinate-major order, is unique and equals the block-diagonal matrix $\frac1{\sqrt n}\operatorname{diag}(\overline L,\dots,\overline L)$. So it is obtained from the Cholesky factor of the $n\times n$ matrix $\overline K$ alone.
--   3. If $\xi\sim\mathcal N(0,I_{nd})$ and $L_{D_K}$ is the lower triangular Cholesky factor of $D_K$, then
--
--   $$\sqrt{2\epsilon_t}\,P^\top L_{D_K}\,\xi\ \sim\ \mathcal N(0,2\epsilon_tK),$$
--
--   which is the law of the noise term of the sSVGD update (24). This is the chain of identities (27).
--
--   **Formalization Note** The paper's "$\sim$" chain (27) mixes random variables and laws. It is stated here as one identity of laws: the image of $\mathcal N(0,I)$ under $\xi\mapsto\sqrt{2\epsilon_t}P^\top L_{D_K}\xi$ is $\mathcal N(0,2\epsilon_tK)$. Positive definiteness of $\overline K$ is the paper's assertion below eq. (22), taken as a hypothesis. The paper's further assumption that $k$ is an inner product of feature maps is used only to obtain that assertion, and is not included.
-- source:
--   Zhang, Lomas, Zhou, Zheng and Curtis, 3D Bayesian Variational Full Waveform Inversion, arXiv:2210.03613v2 (2022), claim c002; Section 2.4 (Stochastic SVGD), eqs. (22), (25), (26), (27), PDF pp. 14-15

import Mathlib
import Definitions.Def_Arxiv2210_03613_Basic

open MeasureTheory ProbabilityTheory InformationTheory

namespace Arxiv2210_03613

theorem ssvgd_noise_block_cholesky {n d : ℕ} (hn : 0 < n)
    (k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (m : Fin n → Fin d → ℝ) (hK : (gramMat k m).PosDef)
    (ε : ℝ) (hε : 0 < ε) (Lbar : Matrix (Fin n) (Fin n) ℝ)
    (hLbar : IsLowerCholesky Lbar (gramMat k m)) :
    permP n d * svgdK k m * (permP n d).transpose = blockDK k m ∧
    (∀ L : Matrix (Lex (Fin d × Fin n)) (Lex (Fin d × Fin n)) ℝ,
      IsLowerCholesky L (blockDK k m) ↔
        L = fun x y => if (ofLex x).1 = (ofLex y).1
          then Lbar (ofLex x).2 (ofLex y).2 / Real.sqrt n else 0) ∧
    (∀ L : Matrix (Lex (Fin d × Fin n)) (Lex (Fin d × Fin n)) ℝ,
      IsLowerCholesky L (blockDK k m) →
        (multivariateGaussian (0 : EuclideanSpace ℝ (Lex (Fin d × Fin n))) 1).map
            (fun ξ => Real.sqrt (2 * ε) • Matrix.toEuclideanLin ((permP n d).transpose * L) ξ) =
          ssvgdNoise ε k m) := by sorry

end Arxiv2210_03613
