-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_pDiff_mean
-- name    : Arxivcond_mat_0004049.pDiff_mean
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T13:57:52.801717+00:00
-- url     : https://prove2.me/theorems/0e35b060-616b-57bd-9a00-ad20b67e3b1b
-- title:
--   The diffusion-theory delay-time density $P_{\rm diff}$ has mean $\bar\varphi'$
-- statement:
--   Let $Q > 0$ and $\bar\varphi' > 0$, and let
--
--   $$
--   P_{\rm diff}(\varphi') = \frac{Q}{2\bar\varphi'}\left[Q + \left(\frac{\varphi'}{\bar\varphi'} - 1\right)^2\right]^{-3/2}
--   $$
--
--   be the diffusion-theory distribution of the single-mode delay time, eq. (17). Then $\varphi' P_{\rm diff}(\varphi')$ is Lebesgue integrable on $\mathbb{R}$ and
--
--   $$
--   \int_{-\infty}^{\infty} \varphi'\, P_{\rm diff}(\varphi')\, d\varphi' = \bar\varphi'.
--   $$
--
--   The paper contrasts this with the localized regime: there the mean $\langle\varphi'\rangle = \langle B_1\rangle$ diverges, while for $P_{\rm diff}$ it is finite and equal to $\bar\varphi'$. This is the diffusive half of milestone "Eqs. (16)-(17), the mean delay time".
--
--   **Formalization Note** $P_{\rm diff}$ is `pDiff Q phibar` from the mission definitions file; integrability is stated separately so that the Bochner integral is the genuine mean.
-- source:
--   H. Schomerus, K. J. H. van Bemmel, C. W. J. Beenakker, Coherent backscattering effect on wave dynamics in a random medium, arXiv:cond-mat/0004049v1 (2000), https://arxiv.org/abs/cond-mat/0004049, p. 3, eq. (17) and the paragraph following it ("the mean ... is finite (equal to $\bar\varphi'$) for $P_{\rm diff}$")

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory Filter Topology

namespace Arxivcond_mat_0004049

theorem pDiff_mean (Q phibar : ℝ) (hQ : 0 < Q) (hphibar : 0 < phibar) :
    Integrable (fun φ : ℝ => φ * pDiff Q phibar φ) ∧
      ∫ φ : ℝ, φ * pDiff Q phibar φ = phibar := by sorry

end Arxivcond_mat_0004049
