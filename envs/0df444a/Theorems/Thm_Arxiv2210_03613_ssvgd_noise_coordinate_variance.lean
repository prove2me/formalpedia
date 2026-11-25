-- Prove2me | Theorems.Thm_Arxiv2210_03613_ssvgd_noise_coordinate_variance
-- name    : Arxiv2210_03613.ssvgd_noise_coordinate_variance
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T16:35:00.588676+00:00
-- url     : https://prove2.me/theorems/32979285-afd7-52bc-903a-c74f87aecfd9
-- title:
--   Remark after eq. (24): the sSVGD noise has variance $2\epsilon_t k(m_i,m_i)/n$ per coordinate (first sentence only)
-- statement:
--   Let $n\ge1$ particles $m_1,\dots,m_n\in\mathbb{R}^d$ and a function $k$ be such that the kernel matrix $\overline K=[k(m_i,m_j)]_{i,j}$ is positive definite, as the paper assumes. Let $\epsilon_t>0$ be the step size, and let $K=\frac1n[k(m_i,m_j)I_{d\times d}]$ be the matrix of eq. (22). Then each coordinate $a$ of the noise $\eta\sim\mathcal N(0,2\epsilon_tK)$ of particle $i$ in the sSVGD update (24) has variance
--
--   $$\operatorname{Var}\big(\eta_{(i,a)}\big)=\frac{2\epsilon_t\,k(m_i,m_i)}{n}.$$
--
--   In particular, if $k(x,x)\le C$ for all $x$, every coordinate of the noise has variance at most $2\epsilon_tC/n$. For the RBF kernel (17), $C=1$.
--
--   This is the precise content of the paper's remark that "when the number of particles is large enough, the noise term would be tiny according to equation (22)".
--
--   **Formalization Note** Only this first sentence of the remark is stated. The second sentence, that sSVGD then "produces the same results as standard SVGD", is not a mathematical statement, and "large enough" is not quantified. Positive definiteness of $\overline K$ is the paper's assertion below eq. (22), taken here as a hypothesis. The variance identity itself needs only positive semidefiniteness.
-- source:
--   Zhang, Lomas, Zhou, Zheng and Curtis, 3D Bayesian Variational Full Waveform Inversion, arXiv:2210.03613v2 (2022), claim c001; Section 2.4 (Stochastic SVGD), remark after eq. (24), with eq. (22), PDF p. 14

import Mathlib
import Definitions.Def_Arxiv2210_03613_Basic

open MeasureTheory ProbabilityTheory InformationTheory

namespace Arxiv2210_03613

theorem ssvgd_noise_coordinate_variance {n d : ℕ} (hn : 0 < n)
    (k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (m : Fin n → Fin d → ℝ) (hK : (gramMat k m).PosDef)
    (ε : ℝ) (hε : 0 < ε) :
    (∀ (i : Fin n) (a : Fin d),
      variance (fun η : EuclideanSpace ℝ (Fin n × Fin d) => η (i, a)) (ssvgdNoise ε k m) =
        2 * ε * k (m i) (m i) / n) ∧
    (∀ C : ℝ, (∀ x, k x x ≤ C) → ∀ (i : Fin n) (a : Fin d),
      variance (fun η : EuclideanSpace ℝ (Fin n × Fin d) => η (i, a)) (ssvgdNoise ε k m) ≤
        2 * ε * C / n) := by sorry

end Arxiv2210_03613
