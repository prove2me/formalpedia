-- Prove2me | Theorems.Thm_CustomReturns_WinWin_solution_2
-- name    : CustomReturns.WinWin.solution_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:16:09.34274+00:00
-- url     : https://prove2.me/theorems/9ebada06-0807-4a53-be63-b502bbd9b131
-- title:
--   Solution 2 of the firm's problem (3)
-- statement:
--   Consider the model's parameter region for Solution 2. Assume $0<\theta$, $\beta_c<1$, $r_s\le\min\{\theta,r_s^{SB2}(r_c)\}$, and $r_c\ge\bar{\bar r}_c(r_s)$. To select the interior solution, also assume $r_s<\theta$, $r_s+\theta\le\mu_s+k_s$, $Q_s^{R,2}>0$, $Q_c^{R,2}>0$, and $Q_s^{R,2}+Q_s^{K,2}+Q_c^{R,2}<1$. Then an optimal policy exists, and every optimal policy has
--
--   $$
--   p_s^*=\frac{k_s+\mu_s}{2},\quad
--   f_s^*=\frac{\mu_s+k_s-r_s-\theta}{2},\quad
--   (Q_s^R,Q_s^K,Q_c^R,Q_c^K)
--   =(Q_s^{R,2},Q_s^{K,2},Q_c^{R,2},0).
--   $$
--
--   The named quantities on the right are the rational expressions printed in Appendix A.2. This characterizes the firm's original optimum in the region used by Proposition 2.
--
--   **Formalization Note** The strict interiority conditions are additional to the printed region conditions. The printed customized price and fee are omitted because the displayed price is inconsistent with the paper's own segment formulas at the rational witness; the segment formulas and standard terms are retained.
-- source:
--   Esenduran, Letizia & Ovchinnikov, Customization and Returns, accepted manuscript (Management Science, accepted Dec. 13, 2021; SSRN 3444244), Online Appendix pp. 4–5 (PDF 20–21), Solution 2 and Table 6

import Mathlib
import Definitions.Def_CustomReturns_WinWin_Model

namespace CustomReturns.WinWin

/-- Solution 2 of problem (3), Online Appendix pp. 4–5. The paper's segment
formulas and standard terms are used; the additional strict interiority conditions
select the advertised solution rather than a boundary or an infeasible stationary point. -/
theorem solution_2 (P : Params)
    (hstanding : P.Standing) (hθ : 0 < P.θ) (hβ : P.βc < 1)
    (hregionS : P.rs ≤ min P.θ (rSB2 P))
    (hregionC : rbarbar_c P ≤ P.rc)
    (hstrictS : P.rs < P.θ)
    (hfeeS : P.rs + P.θ ≤ P.μs + P.ks)
    (hQRs : 0 < QRs2 P) (hQRc : 0 < QRc2 P)
    (hinterior : QRs2 P + QKs2 P + QRc2 P < 1) :
    (∃ x : Policy, IsOptimal P x) ∧
      ∀ x : Policy, IsOptimal P x →
        x.ps = (P.ks + P.μs) / 2 ∧
        x.fs = (P.μs + P.ks - P.rs - P.θ) / 2 ∧
        QRS P x = QRs2 P ∧ QKS P x = QKs2 P ∧
        QRC P x = QRc2 P ∧ QKC P x = 0 := by sorry

end CustomReturns.WinWin
