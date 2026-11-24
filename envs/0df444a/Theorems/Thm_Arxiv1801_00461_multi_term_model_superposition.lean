-- Prove2me | Theorems.Thm_Arxiv1801_00461_multi_term_model_superposition
-- name    : Arxiv1801_00461.multi_term_model_superposition
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:18:34.161255+00:00
-- url     : https://prove2.me/theorems/65594190-e022-4344-9548-b6018ae4fd75
-- title:
--   Eq. (51) (as proved): the apparent conductivity of a sum of power laws
-- statement:
--   Let $\varepsilon_o>0$, $N\in\mathbb N$, real coefficients $\kappa_j$ ($j=1,\dots,N$) and $-1<x_j<1$, and let $\varepsilon_A(\omega)=\varepsilon_o+\sum_{j=1}^N\kappa_j/|\omega|^{2+x_j}$ (eq. (51)). Then for every $\omega>0$
--
--   $$\mathcal H\big(\bar\Delta(\omega\varepsilon_A)\big)(\omega)=\sum_{j=1}^N\frac{K(\kappa_j,x_j)}{\omega^{1+x_j}},$$
--
--   where $K(\kappa_j,x_j)=\frac{2\kappa_j}{\pi}⨍_0^\infty\frac{dy}{(y^2-1)y^{x_j}}$. is the constant $\kappa_1$ of eq. (40) with $\kappa=\kappa_j$, $x=x_j$. Hence $\bar\Delta\sigma_A=-\sum_jK(\kappa_j,x_j)/\omega^{1+x_j}$, and the phase of the apparent admittance follows from the fitted parameters $\kappa_j,x_j$.
--
--   **Formalization Note** The paper states only $x_j>-1$ and says the phase 'can be calculated' by fitting (51) to measurements. The statement gives the mathematical content of that calculation, superposition of the single-term result, for $-1<x_j<1$, where each principal value exists. Fitting to data and the remark that the phase is 'non-negligible' are not included.
-- source:
--   Bédard and Destexhe, Kramers-Kronig relations and the properties of conductivity and permittivity in heterogeneous media, arXiv:1801.00461v1 (2018), claim c024; Sec. 3.1.2, eq. (51) and closing paragraph, PDF p. 15

import Mathlib
import Definitions.Def_Arxiv1801_00461_Basic

open MeasureTheory Filter Topology

namespace Arxiv1801_00461

theorem multi_term_model_superposition {N : ℕ} (eps0 : ℝ) (heps0 : 0 < eps0)
    (kappa x : Fin N → ℝ) (hx1 : ∀ j, -1 < x j) (hx2 : ∀ j, x j < 1) (ω : ℝ) (hω : 0 < ω) :
    HasHilbert (fun a => a * (epsMultiModel eps0 kappa x a - eps0)) ω
      (∑ j, kappaOne (kappa j) (x j) / ω ^ (1 + x j)) := by sorry

end Arxiv1801_00461
