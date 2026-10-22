-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_leftCollisionPoint_mem_leftEnergyComponent
-- name    : BirkhoffGlobalSection.leftCollisionPoint_mem_leftEnergyComponent
-- status  : Proved
-- author  : @Yivy Yu
-- created : 2026-09-12T15:07:49.935689+00:00
-- url     : https://prove2.me/theorems/b348d9a5-a146-4622-9532-a2fadd856a5a
-- title:
--   The selected collision point lies on the energy component
-- statement:
--   Let $0<\mu<1$. For every real energy parameter $c$, the point
--
--   $$
--   (z_1,z_2,w_1,w_2)=(0,0,\sqrt{1-\mu},0)
--   $$
--
--   lies in the selected Levi-Civita component $\Sigma_{\mu,c}$. At this point $D=1$ and $K_{\mu,c}=0$, so it is the regularized collision used to anchor the component definition.
-- source:
--   Joung--van Koert, equation (2.2), https://arxiv.org/abs/2407.19159v3. Membership of the chosen point follows by direct substitution and anchors the source's selected component.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- The designated regularized collision point lies on the selected component
for physical mass parameters. -/
theorem leftCollisionPoint_mem_leftEnergyComponent (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    leftCollisionPoint μ ∈ leftEnergyComponent μ c := by sorry

end BirkhoffGlobalSection
