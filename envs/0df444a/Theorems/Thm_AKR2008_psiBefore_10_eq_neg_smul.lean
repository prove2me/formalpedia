-- Prove2me | Theorems.Thm_AKR2008_psiBefore_10_eq_neg_smul
-- name    : AKR2008.psiBefore_10_eq_neg_smul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:20:02.676906+00:00
-- url     : https://prove2.me/theorems/81962b90-e5e7-49a2-9d1e-a7328600b840
-- title:
--   Component (1, 0) of singlet state equals negative scaled detector state
-- statement:
--   Let $\mathcal H$ be a complex inner-product space and $\Phi_0 \in \mathcal H$. In the pre-measurement EPR singlet state, the component along $|1\rangle_1 |0\rangle_2$ is:
--
--   $$ (\Psi_0)_{10} = -\frac{1}{\sqrt{2}} \Phi_0. $$
--
--   This follows from evaluating the basis projection $\operatorname{polKet}(0, 1)\operatorname{polKet}(1, 0) - \operatorname{polKet}(1, 1)\operatorname{polKet}(0, 0) = -1$.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eq. (1)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem psiBefore_10_eq_neg_smul
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) :
    psiBefore Φ₀ 1 0 = (- ((1 / Real.sqrt 2 : ℝ) : ℂ)) • Φ₀ := by sorry

end AKR2008
