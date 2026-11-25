-- Prove2me | Theorems.Thm_Arxiv1408_1879_neumann_series_solution
-- name    : Arxiv1408_1879.neumann_series_solution
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T11:42:10.158784+00:00
-- url     : https://prove2.me/theorems/62ded5e0-0aff-4343-87ed-b5f494cfcb08
-- title:
--   Eqs. (11)-(12): the series of Volterra operators converges when R is small
-- statement:
--   Let $E$ be a complex Banach space and $L:E\to E$ a bounded linear operator with bounded inverse. There is a $\delta>0$ with the following property. Let $R:E\to E$ be bounded linear and $\psi_i\in E$, and write $\varphi_n=(L^{-1}R)^nL^{-1}\psi_i$ for the terms of the series (12). If
--   $$\|R\varphi_n\|\le\delta\,\|\varphi_n\|\quad\text{for every }n,$$
--   then the series
--   $$\frac{\partial\psi}{\partial z}=\Big[L^{-1}-L^{-1}RL^{-1}+(L^{-1}R)^2L^{-1}-\cdots\Big]\psi_i=\sum_{n\ge0}(-1)^n\varphi_n$$
--   converges, and its sum $u$ solves the integral equation (10), $(L+R)u=\psi_i$.
--
--   This is the paper's iterative solution. Each term is a product of the one-sided operators $L^{-1}$ and $R$, and the series may be truncated once $R$ is small.
--
--   **Formalization Note** The paper states its smallness condition as "$\|R\phi\|/\|\phi\|$ is small for all terms $\phi$ in the series". Here it is a bound $\|R\varphi_n\|\le\delta\|\varphi_n\|$ with a threshold $\delta$ that depends only on $L$. The paper gives no function space, so the statement is made for bounded operators on an arbitrary complex Banach space.
-- source:
--   M. Spivack and O. Rath Spivack, Rough surface backscatter and statistics via extended parabolic integral equation, arXiv:1408.1879v2 (2015), claim c003; Section 3.2, eqs. (11), (12) and the paragraph after (12), PDF p. 6

import Mathlib
import Definitions.Def_Arxiv1408_1879_Basic

open MeasureTheory Filter Topology

namespace Arxiv1408_1879

theorem neumann_series_solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (L : E ≃L[ℂ] E) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (R : E →L[ℂ] E) (ψi : E),
      (∀ n : ℕ, ‖R (seriesTerm L R ψi n)‖ ≤ δ * ‖seriesTerm L R ψi n‖) →
      ∃ u : E, HasSum (fun n : ℕ => (-1 : ℂ) ^ n • seriesTerm L R ψi n) u ∧
        (L : E →L[ℂ] E) u + R u = ψi := by sorry

end Arxiv1408_1879
