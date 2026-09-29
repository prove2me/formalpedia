-- Prove2me | Theorems.Thm_CODATA2022_chiSquare_weight_smul
-- name    : CODATA2022.chiSquare_weight_smul
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T23:22:24.993559+00:00
-- url     : https://prove2.me/theorems/a0298664-cd7f-4487-b3d1-7471f89ec7b6
-- title:
--   $\chi^2$ scales linearly in the weight matrix
-- statement:
--   Multiplying all uncertainties by an **expansion factor** $f$ multiplies the
--   covariance matrix by $f^2$ and hence the weight matrix by $f^{-2}$. The underlying
--   elementary fact is that $\chi^2$ is linear in the weight matrix:
--
--   $$\chi^2_{cW}(x) \;=\; c\,\chi^2_W(x)\qquad\text{for every scalar }c.$$
--
--   In particular the set of minimizers is unchanged for $c>0$: expansion factors rescale the
--   reported $\chi^2$ and the Birge ratio without moving the recommended values.
-- source:
--   Mohr, Newell, Taylor, Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, Rev. Mod. Phys. 97, 025002 (2025), https://doi.org/10.1103/RevModPhys.97.025002, Sec. I.B.12 and Sec. XIV.A: expansion factors 1.7, 2.5 and 3.9 applied to the uncertainties of groups of input data.

import Mathlib
import Definitions.Def_CODATA2022_least_squares
open Matrix

namespace CODATA2022
theorem chiSquare_weight_smul {N M : ℕ} (A : Matrix (Fin N) (Fin M) ℝ)
    (W : Matrix (Fin N) (Fin N) ℝ) (z : Fin N → ℝ) (x : Fin M → ℝ) (c : ℝ) :
    chiSquare A (c • W) z x = c * chiSquare A W z x := by sorry
end CODATA2022
