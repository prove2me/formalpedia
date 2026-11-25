-- Prove2me | Theorems.Thm_Arxiv2412_03183_extended_functions_on_diagonal
-- name    : Arxiv2412_03183.extended_functions_on_diagonal
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T14:00:16.972023+00:00
-- url     : https://prove2.me/theorems/be8e509c-f749-4a91-8501-55ee5ed15b85
-- title:
--   Eqs. (A1)-(A2): the extended functions reduce to $L$ and $S$ at $h=g$
-- statement:
--   For every non-negative image $x$, all gains $g$ and all $\mu_1,\mu_2\ge0$, setting $h=g$ in the extended functions of eqs. (A1)-(A2) gives
--
--   $$\mathcal{L}_{\tilde v}(x,g,g)=L_{\tilde v}(x,g),\qquad\mathcal{S}_{\mu_1,\mu_2}(g,g)=S_{\mu_1,\mu_2}(g).$$
-- source:
--   Ikeda, Nakazato, Tsukagoshi, Takeuchi and Yamaguchi, Solving Self-calibration of ALMA Data with an Optimization Method, arXiv:2412.03183v1 (2024), claim c019; Appendix 1, eqs. (A1)-(A2) and the sentence after them, PDF p. 9

import Mathlib
import Definitions.Def_Arxiv2412_03183_Basic

open Finset

namespace Arxiv2412_03183

theorem extended_functions_on_diagonal {S : Type*} [Fintype S] [DecidableEq S] {N : S → ℕ}
    {M Nx Ny : ℕ} (D : ObsSetup S N M Nx Ny) (x : Image Nx Ny) (hx : x ∈ nonnegImages)
    (g : Gains N) (mu1 mu2 : ℝ) (hmu1 : 0 ≤ mu1) (hmu2 : 0 ≤ mu2) :
    extDataLoss D x g g = dataLoss D x g ∧ extGainReg D mu1 mu2 g g = gainReg D mu1 mu2 g := by sorry

end Arxiv2412_03183
