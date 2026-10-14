-- Prove2me | Theorems.Thm_DbarRegularity_norm_inv_norm_smul_sub_le
-- name    : DbarRegularity.norm_inv_norm_smul_sub_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T19:28:29.528983+00:00
-- url     : https://prove2.me/theorems/585ec8be-5f7e-4a1c-adb6-dec70c08a995
-- title:
--   Distance between radial projections onto the unit sphere
-- statement:
--   Let $E$ be a real normed space, $u,v\in E$ and $v\ne0$. Then
--   $$\Bigl\|\frac{u}{\|u\|}-\frac{v}{\|v\|}\Bigr\|\;\le\;\frac{2\,\|u-v\|}{\|v\|},$$
--   with the convention $u/\|u\|=0$ for $u=0$.
--
--   **Formalization Note.** $u/\|u\|$ is written `‖u‖⁻¹ • u`; in Lean `(0 : ℝ)⁻¹ = 0`, which gives the convention at $u=0$, where the bound reads $1\le2$.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter II, § 4.2, Theorem 3, p. 39

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace DbarRegularity

/-- Distance between the radial projections to the unit sphere: for `v ≠ 0`,
`|u/|u| - v/|v|| ≤ 2 |u - v| / |v|` (with `0/|0| = 0`). -/
theorem norm_inv_norm_smul_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v : E) (hv : v ≠ 0) :
    ‖‖u‖⁻¹ • u - ‖v‖⁻¹ • v‖ ≤ 2 * ‖u - v‖ / ‖v‖ := by sorry

end DbarRegularity
