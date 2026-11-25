-- Prove2me | Theorems.Thm_Arxiv1707_02146_shorter_focus_wider_correlation_bandwidth
-- name    : Arxiv1707_02146.shorter_focus_wider_correlation_bandwidth
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T00:28:24.860328+00:00
-- url     : https://prove2.me/theorems/895070f4-4a0a-48fe-8ad4-3933613d19f4
-- title:
--   p. 3: a shorter focus duration $\tau_f<\tau_m$ gives a larger spectral correlation bandwidth $\delta\lambda_f>\delta\lambda_m$
-- statement:
--   Suppose the traversal time and the spectral correlation bandwidth are related by $\tau=\kappa/\delta\lambda$ with one constant $\kappa>0$, both for the medium ($\tau_m=\kappa/\delta\lambda_m$) and for the focus ($\tau_f=\kappa/\delta\lambda_f$), where $\delta\lambda_m,\delta\lambda_f>0$. If $\tau_f<\tau_m$, then
--   $$\delta\lambda_f>\delta\lambda_m.$$
--
--   **Formalization Note** The paper states $\tau_m\propto1/\delta\lambda_m$ for the medium only (p. 2); applying the same relation, with the same constant, at the focus is the reading under which "a decrease of $\tau_f$ leads to" a larger $\delta\lambda_f$. The paper's corroborating spectral measurement is not shown and is not part of the statement.
-- source:
--   Mounaix, de Aguiar and Gigan, Temporal recompression through a scattering medium via a broadband transmission matrix, arXiv:1707.02146v1 (2017), claim c012; main text, end of the paragraph explaining the factor 2 (tex l. 90), with tau_m proportional to 1/delta_lambda_m from p. 2 (tex l. 41), PDF pp. 2-3

import Mathlib
import Definitions.Def_Arxiv1707_02146_Basic

open Matrix ComplexConjugate

namespace Arxiv1707_02146

theorem shorter_focus_wider_correlation_bandwidth (κ bwm bwf : ℝ) (hκ : 0 < κ)
    (hbwm : 0 < bwm) (hbwf : 0 < bwf)
    (hτ : traversalTime κ bwf < traversalTime κ bwm) :
    bwm < bwf := by sorry

end Arxiv1707_02146
