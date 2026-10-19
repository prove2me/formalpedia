-- Prove2me | Theorems.Thm_CustomReturns_WinWin_solution_2b
-- name    : CustomReturns.WinWin.solution_2b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:16:06.750181+00:00
-- url     : https://prove2.me/theorems/f8419c1d-c0bf-43b0-8dc4-90c897bceb02
-- title:
--   Solution 2b when customized returns are disallowed
-- statement:
--   In the strict Solution 2 region above, assume also $r_s\ge r_s^{SB1}$. Fix any optimal policy of the original firm problem. If customized product returns are disallowed while that policy's standard price and fee are held fixed, a counterfactual optimal policy exists. Every such counterfactual optimum has no customized sales, and its standard-product segments satisfy
--
--   $$
--   Q_s^R=\frac{\mu_s r_s-k_s\theta}{2\theta m_s},
--   \qquad Q_s^K=\frac{\theta-r_s}{2\theta}.
--   $$
--
--   This is the Solution 2b branch used to compare total returns. The assertion concerns the segments and does not claim a unique customized price.
--
--   **Formalization Note** The disallow counterfactual maximizes over every nonnegative customized price and fee with $R_c=0$, keeping the original optimum's standard terms fixed. The page displays the least price that eliminates customized sales; larger prices can give the same optimum. The theorem carries the explicit interiority conditions from Solution 2.
-- source:
--   Esenduran, Letizia & Ovchinnikov, Customization and Returns, accepted manuscript (Management Science, accepted Dec. 13, 2021; SSRN 3444244), proof of Proposition 2, Online Appendix p. 15 (PDF 31), Solution 2b and problem (5)

import Mathlib
import Definitions.Def_CustomReturns_WinWin_Model

namespace CustomReturns.WinWin

/-- Solution 2b of problem (5), proof of Proposition 2, Online Appendix p. 15.
The paper's price is the least price that excludes customized sales; the
counterfactual optimum need not have a unique customized price. -/
theorem solution_2b (P : Params)
    (hstanding : P.Standing) (hθ : 0 < P.θ) (hβ : P.βc < 1)
    (hregionS : P.rs ≤ min P.θ (rSB2 P))
    (hregionC : rbarbar_c P ≤ P.rc)
    (hstrictS : P.rs < P.θ)
    (hfeeS : P.rs + P.θ ≤ P.μs + P.ks)
    (hQRs : 0 < QRs2 P) (hQRc : 0 < QRc2 P)
    (hinterior : QRs2 P + QKs2 P + QRc2 P < 1)
    (hcase : rSB1 P ≤ P.rs) :
    ∀ x : Policy, IsOptimal P x →
      (∃ y : Policy, IsOptimalNoCReturns P x y) ∧
      ∀ y : Policy, IsOptimalNoCReturns P x y →
        QC P y = 0 ∧ QRS P y = QRs2b P ∧ QKS P y = QKs2 P := by sorry

end CustomReturns.WinWin
