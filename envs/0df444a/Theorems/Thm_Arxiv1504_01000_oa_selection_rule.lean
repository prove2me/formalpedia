-- Prove2me | Theorems.Thm_Arxiv1504_01000_oa_selection_rule
-- name    : Arxiv1504_01000.oa_selection_rule
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T18:40:39.731975+00:00
-- url     : https://prove2.me/theorems/a4a87399-0673-42f1-859f-d4f9a8e86e40
-- title:
--   Section III, Algorithm 1: the selection rule $d_{H\phi_3}>d_{H\phi_2}$ picks exactly the rotation minimising $T_{33}(\theta)$
-- statement:
--   Let $[T]$ be a $3\times3$ Hermitian positive definite coherency matrix with $\Re T_{23}\neq0$, and let $L>0$. Call $\phi\in[-\pi/4,\pi/4]$ a candidate angle if $\phi\in\{\phi_{3,2},\phi_{3,2}\pm\pi/4\}$ for a maximiser $\phi_{3,2}$ over $[-\pi/4,\pi/4]$ of $d_H(\sigma_3^2,\sigma_3^2(\theta))$ or of $d_H(\sigma_2^2,\sigma_2^2(\theta))$, as in eq. (9). Then:
--
--   1. at a candidate angle $\phi$,
--   $$d_H(\sigma_3^2,\sigma_3^2(\phi))>d_H(\sigma_2^2,\sigma_2^2(\phi))\iff T_{33}(\phi)=\min_{\theta\in\mathbb{R}}T_{33}(\theta),$$
--   $$d_H(\sigma_3^2,\sigma_3^2(\phi))<d_H(\sigma_2^2,\sigma_2^2(\phi))\iff T_{33}(\phi)=\max_{\theta\in\mathbb{R}}T_{33}(\theta),$$
--   so the selection criterion of Algorithm 1 holds exactly at the peak where the cross-polarised component is minimised, and the other peak is where it is maximised;
--   2. some candidate angle satisfies the criterion;
--   3. for every selected $\phi$, the final OA $\theta_0$ of eq. (10) lies in $[-\pi/8,\pi/8]$.
--
--   **Formalization Note** The hypothesis $\Re T_{23}\neq0$ is not in the paper. Without it the claim is false. For $[T]=\mathrm{diag}(1,1,2)$ the two distances are equal at the $T_{33}$-minimising peak $\theta=\pm\pi/4$, so no candidate satisfies the strict criterion. The candidates $\phi_{3,2}\pm\pi/4$ are checked as in the text of Section III; Algorithm 1 compares the distances only at $\phi_{3,2}$. The statement does not assert that $\theta_0$ minimises $T_{33}$, because the paper does not claim it.
-- source:
--   Bhattacharya, Muhuri, De, Manickam and Frery, Modifying the Yamaguchi Four-Component Decomposition Scattering Powers Using a Stochastic Distance, arXiv:1504.01000v1 (2015), claim c002 (b), (c); Sec. III, eqs. (7), (9), (10) and Algorithm 1, PDF pp. 3-4

import Mathlib
import Definitions.Def_Arxiv1504_01000_Basic

open MeasureTheory Filter Topology
open scoped ComplexOrder

namespace Arxiv1504_01000

theorem oa_selection_rule (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.PosDef) (L : ℝ) (hL : 0 < L)
    (hRe : (T 1 2).re ≠ 0) :
    (∀ φ, IsCandidateOA T L φ →
      (dH T L 1 φ < dH T L 2 φ ↔ ∀ θ : ℝ, sigmaSq T 2 φ ≤ sigmaSq T 2 θ) ∧
      (dH T L 2 φ < dH T L 1 φ ↔ ∀ θ : ℝ, sigmaSq T 2 θ ≤ sigmaSq T 2 φ)) ∧
    (∃ φ, IsSelectedOA T L φ) ∧
    (∀ φ, IsSelectedOA T L φ → wrapOA φ ∈ Set.Icc (-(Real.pi / 8)) (Real.pi / 8)) := by sorry

end Arxiv1504_01000
