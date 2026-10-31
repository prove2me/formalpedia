-- Prove2me | Theorems.Thm_ContingentSourcing_Competition_proposition_1
-- name    : ContingentSourcing.Competition.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:01.06199+00:00
-- url     : https://prove2.me/theorems/efc4a025-62c4-420e-b87f-0618b542f38f
-- title:
--   Proposition 1, p. 13 — the buyer's optimal orders in the contingent, mixed, diversification and sole-sourcing price regions (Table 1)
-- statement:
--   Consider the buyer's problem (2) at signal accuracy $\rho\in[0,1]$ and prices with $0\le w_U\le m$ and $0\le w_R\le w_E\le m$. Let
--   $$\eta_1(w_U,w_E)=P_1w_U+P_Bw_E+P_GP_{0G}m,\qquad \eta_2(w_U,w_E)=P_1w_U+P_0w_E .$$
--   Then the Table 1 order of the corresponding case is optimal for (2):
--
--   1. if $\eta_1<w_R$: contingent sourcing, $Q_U=(m-w_U)/2$, $Q_R=0$, $Q_E(B)=(m-w_E)/2$;
--   2. if $\eta_2<w_R\le\eta_1$: mixed sourcing, $Q_U=\frac{w_R-P_Gw_U-P_Bw_E}{2P_GP_{0G}}$, $Q_R=\frac{P_GP_{0G}m-w_R+P_Bw_E+P_1w_U}{2P_GP_{0G}}$, $Q_E(B)=\frac{w_R-P_1w_U-P_0w_E}{2P_GP_{0G}}$;
--   3. if $w_U<w_R\le\eta_2$: diversification, $Q_U=\frac{w_R-w_U}{2P_0}$, $Q_R=\frac{P_0m-w_R+P_1w_U}{2P_0}$, $Q_E=0$;
--   4. if $w_R\le w_U$: sole sourcing from R, $Q_U=Q_E=0$, $Q_R=(m-w_R)/2$;
--
--   in each case with $Q_E(G)=0$.
--
--   This is the buyer's response that drives the suppliers' payoffs (5)–(6) in the pricing game.
--
--   **Formalization Note.** Nonnegative $w_U,w_R$ and $0\le\rho\le1$ are added (see Lemma 1). The printed case inequalities are kept, with (i) strict.
-- source:
--   Lu & Tomlin, Forewarned Is Forearmed?, SSRN 4260604 author manuscript (1 May 2023) of MSOM doi:10.1287/msom.2021.0540, p. 13 (PDF 13), Proposition 1 and Table 1

import Mathlib
import Definitions.Def_ContingentSourcing_Competition_Model

namespace ContingentSourcing.Competition

/-- Proposition 1, p. 13: the Table 1 orders are optimal for (2) in the contingent (i), mixed (ii),
diversification (iii) and sole-sourcing (iv) price regions. Nonnegative prices and 0 ≤ ρ ≤ 1 are added. -/
theorem proposition_1 (P : Params) (hP : P.Standing) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (w : Prices) (hwU0 : 0 ≤ w.wU) (hwUm : w.wU ≤ P.m) (hwR0 : 0 ≤ w.wR) (hRE : w.wR ≤ w.wE)
    (hwEm : w.wE ≤ P.m) :
    (P.eta1 ρ w < w.wR → P.IsOptimalOrder ρ w (P.orderI w)) ∧
    (P.eta2 w < w.wR → w.wR ≤ P.eta1 ρ w → P.IsOptimalOrder ρ w (P.orderII ρ w)) ∧
    (w.wU < w.wR → w.wR ≤ P.eta2 w → P.IsOptimalOrder ρ w (P.orderIII w)) ∧
    (w.wR ≤ w.wU → P.IsOptimalOrder ρ w (P.orderIV w)) := by sorry

end ContingentSourcing.Competition
