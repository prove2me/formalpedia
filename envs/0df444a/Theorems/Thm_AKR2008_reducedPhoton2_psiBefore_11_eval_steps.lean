-- Prove2me | Theorems.Thm_AKR2008_reducedPhoton2_psiBefore_11_eval_steps
-- name    : AKR2008.reducedPhoton2_psiBefore_11_eval_steps
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:19:57.38621+00:00
-- url     : https://prove2.me/theorems/6d52980e-cc0d-4ff9-a9fc-888b24211ebc
-- title:
--   Evaluation of reduced photon 2 state (1, 1) entry from components
-- statement:
--   Let $\mathcal H$ be a complex inner-product space and $\Phi_0 \in \mathcal H$ a unit vector ($\Vert\Phi_0\Vert = 1$). If the parallel component vanishes ($(\Psi_0)_{11} = 0$) and the orthogonal component is $(\Psi_0)_{01} = \frac{1}{\sqrt{2}} \Phi_0$, then the vertical reduced state entry evaluates to $1/2$:
--
--   $$ (\rho_2(\Psi_0))_{11} = \tfrac{1}{2}. $$
--
--   This sums the inner products $\langle (\Psi_0)_{01}, (\Psi_0)_{01}\rangle_{\mathcal H} + \langle (\Psi_0)_{11}, (\Psi_0)_{11}\rangle_{\mathcal H} = |1/\sqrt{2}|^2 \Vert\Phi_0\Vert^2 + 0 = 1/2$.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eqs. (1) and (3)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem reducedPhoton2_psiBefore_11_eval_steps
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1)
    (h_zero : psiBefore Φ₀ 1 1 = 0)
    (h_comp : psiBefore Φ₀ 0 1 = ((1 / Real.sqrt 2 : ℝ) : ℂ) • Φ₀) :
    reducedPhoton2 (psiBefore Φ₀) 1 1 = 1 / 2 := by sorry

end AKR2008
