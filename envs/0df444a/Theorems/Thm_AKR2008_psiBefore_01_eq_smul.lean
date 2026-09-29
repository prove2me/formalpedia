-- Prove2me | Theorems.Thm_AKR2008_psiBefore_01_eq_smul
-- name    : AKR2008.psiBefore_01_eq_smul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:19:49.251405+00:00
-- url     : https://prove2.me/theorems/d63e5069-9636-42bd-86de-34bb66ba8e45
-- title:
--   Component (0, 1) of singlet state equals scaled detector state
-- statement:
--   Let $\mathcal H$ be a complex inner-product space and $\Phi_0 \in \mathcal H$. In the pre-measurement EPR singlet state, the component along $|0\rangle_1 |1\rangle_2$ is:
--
--   $$ (\Psi_0)_{01} = \frac{1}{\sqrt{2}} \Phi_0. $$
--
--   This follows from evaluating the basis projection $\operatorname{polKet}(0, 0)\operatorname{polKet}(1, 1) - \operatorname{polKet}(1, 0)\operatorname{polKet}(0, 1) = 1$.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eq. (1)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem psiBefore_01_eq_smul
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) :
    psiBefore Φ₀ 0 1 = ((1 / Real.sqrt 2 : ℝ) : ℂ) • Φ₀ := by sorry

end AKR2008
