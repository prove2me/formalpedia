-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_K_eq_fiber
-- name    : BirkhoffGlobalSection.TangentialHessian.K_eq_fiber
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-29T22:43:04.504019+00:00
-- url     : https://prove2.me/theorems/70f065d4-3d4f-4737-8805-aea8332efddc
-- title:
--   The energy fiber of the Levi-Civita Hamiltonian is a circle in the shifted momentum
-- statement:
--   For all $\mu, c, r$ and every phase point $s = (z_1, z_2, w_1, w_2)$, the Levi-Civita regularized Hamiltonian satisfies
--   $$K_{\mu,c}(s) = P_{\mu,c}(s) - \frac{\mu Z}{r} = \tfrac12 |u|^2 - \tfrac12 F(z),$$
--   where $u = (g_2, g_3) = w + b(z)$ is the $w$-part of the gradient $g = \nabla K$ and $F$ is the squared fiber radius.
--
--   So the energy fiber $K = 0$ over $z$ is the circle $|u|^2 = F$ in the momentum plane. This identity holds with $r$ a free parameter.
--
--   **Formalization note.** $u$ is `(kGradR μ c r s 2, kGradR μ c r s 3)` and $F$ is `fibF μ c r s`.
-- source:
--   Grisa, companion paper, Zenodo 21376299 (2026), §5 (block-diagonal Hessian); Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4, eq. (4.1).

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian_Fiber

namespace BirkhoffGlobalSection.TangentialHessian

/-- The fiber identity `K = |u|²/2 - F/2`, for every `r`. -/
theorem K_eq_fiber (μ c r : ℝ) (s : Phase) :
    pP μ c s - μ * (zNormSq s / r) =
      (kGradR μ c r s 2 ^ 2 + kGradR μ c r s 3 ^ 2) / 2 - fibF μ c r s / 2 := by sorry

end BirkhoffGlobalSection.TangentialHessian
