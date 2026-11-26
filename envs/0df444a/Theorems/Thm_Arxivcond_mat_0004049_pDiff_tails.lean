-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_pDiff_tails
-- name    : Arxivcond_mat_0004049.pDiff_tails
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T13:57:58.941455+00:00
-- url     : https://prove2.me/theorems/8ad53025-5d79-414a-8e4e-d6a8c6a79877
-- title:
--   The tails of $P_{\rm diff}$ decay as $|\varphi'|^{-3}$
-- statement:
--   Let $Q > 0$ and $\bar\varphi' > 0$, and let
--
--   $$
--   P_{\rm diff}(\varphi') = \frac{Q}{2\bar\varphi'}\left[Q + \left(\frac{\varphi'}{\bar\varphi'} - 1\right)^2\right]^{-3/2}
--   $$
--
--   be the diffusion-theory distribution of the single-mode delay time, eq. (17). Then both tails decay as $|\varphi'|^{-3}$ with the same constant:
--
--   $$
--   \lim_{\varphi' \to +\infty} |\varphi'|^3 P_{\rm diff}(\varphi') = \lim_{\varphi' \to -\infty} |\varphi'|^3 P_{\rm diff}(\varphi') = \frac{Q\,\bar\varphi'^2}{2}.
--   $$
--
--   The paper states that in the tails the localized-regime distribution decays as $|\varphi'|^{-2}$ while $P_{\rm diff}$ decays as $|\varphi'|^{-3}$. This lemma is the diffusive half of milestone "Eqs. (16)-(17), tails of the delay-time distributions", with the constant made explicit.
-- source:
--   H. Schomerus, K. J. H. van Bemmel, C. W. J. Beenakker, Coherent backscattering effect on wave dynamics in a random medium, arXiv:cond-mat/0004049v1 (2000), https://arxiv.org/abs/cond-mat/0004049, p. 3, eq. (17) and the sentence "In the tails $P$ decays $\propto |\varphi'|^{-2}$, while $P_{\rm diff} \propto |\varphi'|^{-3}$"

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory Filter Topology

namespace Arxivcond_mat_0004049

theorem pDiff_tails (Q phibar : ℝ) (hQ : 0 < Q) (hphibar : 0 < phibar) :
    Tendsto (fun φ => |φ| ^ 3 * pDiff Q phibar φ) atTop (𝓝 (Q * phibar ^ 2 / 2)) ∧
      Tendsto (fun φ => |φ| ^ 3 * pDiff Q phibar φ) atBot (𝓝 (Q * phibar ^ 2 / 2)) := by sorry

end Arxivcond_mat_0004049
