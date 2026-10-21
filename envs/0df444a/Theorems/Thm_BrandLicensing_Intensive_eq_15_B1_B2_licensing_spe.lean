-- Prove2me | Theorems.Thm_BrandLicensing_Intensive_eq_15_B1_B2_licensing_spe
-- name    : BrandLicensing.Intensive.eq_15_B1_B2_licensing_spe
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:10.011363+00:00
-- url     : https://prove2.me/theorems/af04fa55-776c-4b13-b3df-34f9ed20af70
-- title:
--   Eqs. (15), (B.1), (B.2), pp. 3188, 3195 — the licensing equilibrium: core effort, royalty and licensee effort
-- statement:
--   Under the standing assumptions, let $D=4-[3-(2-\alpha)\alpha]\rho$. The licensing game has a subgame-perfect equilibrium, and in every subgame-perfect equilibrium the core effort and the licensee's equilibrium effort are
--   $$e^L_C=\mu\,\frac{4-\rho[2-\lambda(1-\alpha)^2]}{4-\rho[3-\alpha(2-\alpha)]},\qquad e^L_E=\frac{(1-\alpha)(\lambda+1)\mu\rho}{D}.$$
--   If moreover $\rho>0$ and $\alpha<1$, the equilibrium royalty is
--   $$s^L=\frac{(1-\alpha)\mu\{2-\rho-\lambda\{2-\rho[2-(2-\alpha)\alpha]\}\}}{D}.$$
--
--   These are the licensing counterparts of (A.1)–(A.2); comparing them at the intensive margin is the content of Proposition 3.
--
--   **Formalization Note** The equilibrium is subgame-perfect: the licensee's rule and the royalty rule are optimal in every subgame, not only on the equilibrium path. When $\rho=0$ or $\alpha=1$ the royalty does not affect any payoff, so $s^L$ is not determined; the hypotheses $\rho>0$, $\alpha<1$ are added for (B.1) only. The existence clause is implicit in the paper's derivation.
-- source:
--   Bacchiega, Colucci, Denicolò & Magnani, Only the Ugly Face? A Theoretical Model of Brand Dilution, Management Science 70(5) (2024), p. 3188 (PDF 8), §4.2.2.3, eq. (15); p. 3195 (PDF 15), Appendix B, eqs. (B.1), (B.2)

import Mathlib
import Definitions.Def_BrandLicensing_Intensive_Model

namespace BrandLicensing.Intensive

/-- (15), (B.1), (B.2), pp. 3188, 3195: a subgame-perfect equilibrium of the licensing game exists;
in every one the core effort is (15) and the licensee's effort is (B.2), and, when `ρ > 0` and
`α < 1`, the royalty is (B.1). -/
theorem eq_15_B1_B2_licensing_spe (P : Params) (hP : P.Standing) :
    (∃ σ : LicProfile, IsLicensingSPE P σ) ∧
    ∀ σ : LicProfile, IsLicensingSPE P σ →
      σ.eC = eCL_cf P ∧ σ.eEL = eEL_cf P ∧ (0 < P.ρ → P.α < 1 → σ.sL = sL_cf P) := by sorry
end BrandLicensing.Intensive
