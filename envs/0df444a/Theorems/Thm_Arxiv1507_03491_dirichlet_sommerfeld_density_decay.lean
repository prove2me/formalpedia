-- Prove2me | Theorems.Thm_Arxiv1507_03491_dirichlet_sommerfeld_density_decay
-- name    : Arxiv1507_03491.dirichlet_sommerfeld_density_decay
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T16:58:39.937799+00:00
-- url     : https://prove2.me/theorems/c1b6aee7-1f39-4c4a-b68e-f5d135ef88a6
-- title:
--   Theorem 2.2: the Dirichlet Sommerfeld density decays superalgebraically, independent of $h$
-- statement:
--   Let $\operatorname{Re}k>0$, $\operatorname{Im}k\ge0$ and $M_0>4$, and let $W=W_{M_0}$ be the bump window (2.9). For a point source at $(0,h)$, $h>0$, let $\hat\xi_W^{(h)}$ be the Sommerfeld density (2.13) of the Dirichlet hybrid representation (2.12):
--
--   $$\hat\xi_W^{(h)}(\lambda)=-2\Big(F_h(\lambda)-\frac1{2\pi}\int_{\mathbb R}\hat W(\lambda-\mu)F_h(\mu)\,d\mu\Big),\qquad F_h(\lambda)=\frac{e^{-\sqrt{\lambda^2-k^2}\,h}}{\sqrt{\lambda^2-k^2}}.$$
--
--   Then $|\hat\xi_W^{(h)}(\lambda)|$ decays superalgebraically, independently of $h$: for every $n\in\mathbb N$ there are constants $C,R$ such that
--
--   $$|\lambda|^n\,\big|\hat\xi_W^{(h)}(\lambda)\big|\le C\qquad\text{for all }h>0\text{ and all }|\lambda|\ge R.$$
--
--   This is the paper's justification that the Sommerfeld correction can be truncated to a fixed frequency interval however close the source is to the interface.
--
--   **Formalization Note** "Independent of $h$" is read as constants $C,R$ that are uniform in $h>0$. $R$ is needed because for real $k$ the density has integrable singularities at $\lambda=\pm k$. The density printed in (2.13) is twice the one that makes (2.12) hold (see eqs. (2.12)–(2.13) as derived); the constant factor does not affect decay.
-- source:
--   Lai, Greengard and O'Neil, A new hybrid integral representation for frequency domain scattering in layered media, arXiv:1507.03491v2 (2015), claim c005; Section 2, Theorem 2.2 with eq. (2.13), PDF pp. 8–9

import Mathlib
import Definitions.Def_Arxiv1507_03491_Basic

open MeasureTheory Filter Topology Set
open scoped ContDiff NNReal

namespace Arxiv1507_03491

theorem dirichlet_sommerfeld_density_decay (k : ℂ) (hk : 0 < k.re) (hk' : 0 ≤ k.im)
    (M0 : ℝ) (hM0 : 4 < M0) :
    SuperalgDecayUniform (fun h lam => dirSommerfeldDensity M0 k 0 h lam) (Ioi 0) := by sorry

end Arxiv1507_03491
