-- Prove2me | Theorems.Thm_Arxiv2003_13288_far_apart_criterion
-- name    : Arxiv2003_13288.far_apart_criterion
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T08:46:04.631799+00:00
-- url     : https://prove2.me/theorems/231a775f-d65e-4853-8f67-8643cb82ed79
-- title:
--   Sec. 2.3, footnote 5: the second far-apart criterion of independent scattering
-- statement:
--   Let $k>0$ be the wavenumber, $\delta>0$ the mean distance between scatterers and $C_s>0$ the scattering cross section of one scatterer. Take the number density $n_0=1/\delta^3$ and the scattering mean free path $l_s=1/(n_0C_s)$. Then
--
--   $$kl_s=\left(\frac{\delta}{\sqrt[3]{C_s/k}}\right)^3,$$
--
--   so for every threshold $M>0$,
--
--   $$kl_s\ge M\iff\delta\ge M^{1/3}\sqrt[3]{C_s/k}.$$
--
--   This is the paper's statement that the criterion $kl_s\gg1$ becomes $\delta\gg\sqrt[3]{C_s/k}$.
--
--   **Formalization Note** The paper's $n_0\approx1/\delta^3$ is taken as an equality, and "$\gg$" is expressed by an arbitrary threshold $M>0$.
-- source:
--   B. X. Wang and C. Y. Zhao, The dependent scattering effect on radiative properties of micro/nanoscale discrete disordered media, arXiv:2003.13288v1 (2020), claim c002; Sec. 2.3, footnote 5, PDF p. 14

import Mathlib
import Definitions.Def_Arxiv2003_13288_Basic

open MeasureTheory Filter Topology

namespace Arxiv2003_13288

theorem far_apart_criterion (k δ Cs : ℝ) (hk : 0 < k) (hδ : 0 < δ) (hCs : 0 < Cs) :
    k * scatMeanFreePath (1 / δ ^ 3) Cs = (δ / (Cs / k) ^ (1 / 3 : ℝ)) ^ 3 ∧
    ∀ M : ℝ, 0 < M →
      (M ≤ k * scatMeanFreePath (1 / δ ^ 3) Cs ↔ M ^ (1 / 3 : ℝ) * (Cs / k) ^ (1 / 3 : ℝ) ≤ δ) := by sorry

end Arxiv2003_13288
