-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_leviCivita_regularAt_left_collision
-- name    : BirkhoffGlobalSection.leviCivita_regularAt_left_collision
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T18:18:40.055629+00:00
-- url     : https://prove2.me/theorems/7117df3a-f19e-43c4-8044-c9e8c1168cb5
-- title:
--   Regularity at the Levi-Civita left collision
-- statement:
--   Let $0<1-\mu$, let $K_{\mu,c}$ be the Levi-Civita Hamiltonian, and let $s=(z,w)$ be any state over the regularized left collision with $z=0$ and $K_{\mu,c}(s)=0$. Then
--
--   $$
--   dK_{\mu,c}(s)\ne0.
--   $$
--
--   At $z=0$, Equation (2.2) reduces to $K_{\mu,c}=|w|^2/2-(1-\mu)/2$. Thus the zero-energy condition makes $w$ nonzero, and a momentum derivative cannot vanish. The claim applies to any state satisfying these conditions, independently of which connected component is selected.
-- source:
--   Joung--van Koert, Equation (2.2) and Proposition 2.4, https://arxiv.org/abs/2407.19159v3, PDF pp. 6–7. The collision calculation uses the displayed Levi-Civita Hamiltonian; the collision-free case uses its local coordinate relation to the Jacobi Hamiltonian below the first critical value.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- At the regularized left collision `z=0`, the zero-energy condition
forces nonzero `w`, so the Hamiltonian differential cannot vanish. -/
theorem leviCivita_regularAt_left_collision (μ c : ℝ)
    (hμ1 : μ < 1) (s : Phase)
    (hK : leviCivitaHamiltonian μ c s = 0)
    (hz : zNormSq s = 0) :
    fderiv ℝ (leviCivitaHamiltonian μ c) s ≠ 0 := by sorry

end BirkhoffGlobalSection
