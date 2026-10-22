-- Prove2me | Theorems.Thm_FibAnyon_Approx_distance_display
-- name    : FibAnyon.Approx.distance_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:28.543358+00:00
-- url     : https://prove2.me/theorems/feb39ecb-5545-4bc5-836a-e830a0dcced9
-- title:
--   §V distance display, p. 11 (corrected: U[u,v,5])
-- statement:
--   Let $u,v\in\mathbb Z[\omega]$ form an exact unitary, and let $\phi$ be a real rotation angle. The phase-invariant distance from the target rotation to the correctly phased unitary is
--
--   $$d(R_z(\phi),U[u,v,5])=\sqrt{1-|\operatorname{Re}(ue^{i\phi/2})|}.$$
--
--   This formula reduces the matrix approximation condition to the upper-left cyclotomic entry.
--
--   **Formalization Note** The printed display has $U[u,v,0]$, for which the asserted right-hand side is generally false. The phase $5$ is required because $\omega^5=-1$.
-- source:
--   Kliuchnikov, Bocharov, Svore, Asymptotically optimal topological quantum compiling, arXiv:1310.4150v1, p. 11, §V display after eq. (21) (phase corrected)

import Mathlib
import Definitions.Def_FibAnyon_Approx_Model

noncomputable section

namespace FibAnyon.Approx

/-- Corrected phase in the first distance display of §V, p. 11. -/
theorem distance_display (φ : ℝ) (u v : ZOmega) (h : IsExact u v) :
    dist (Rz φ) (exactU u v 5) =
      Real.sqrt (1 - |(u.toC * Complex.exp (φ * Complex.I / 2)).re|) := by sorry

end FibAnyon.Approx
