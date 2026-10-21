-- Prove2me | Theorems.Thm_EndoCredit_Baseline_proposition_3_1
-- name    : EndoCredit.Baseline.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:23.035213+00:00
-- url     : https://prove2.me/theorems/d351fb02-3ea2-43c1-a159-5c9f1f0f9fab
-- title:
--   Proposition 3.1, p. 10 — D* clause — the running-maximum shadow price solves the dual problem (3.4)
-- statement:
--   Fix a Lagrange multiplier $\lambda>0$ with $\lambda\bar I^{\gamma}\le Q^{-\gamma}$, and let $y_t=\lambda e^{\beta t}H_tI_t^{\gamma}$ be the income-adjusted dual process. Define the shadow price
--   $$D^\lambda_t=\max\Big(0,\ \max_{0\le s\le t}Q^\gamma y_s-1\Big),\qquad t\ge0 .$$
--   Under the standing assumptions of the baseline model, $D^\lambda$ is an admissible shadow-price process (adapted, non-decreasing, continuous, $D^\lambda_0=0$, and satisfying the integrability conditions (3.2)), and it minimizes the dual objective of (3.4) over all admissible shadow-price processes for this $\lambda$.
--
--   This is the shadow-price clause of Proposition 3.1: the dual minimization is solved by a reflection of the dual process at the level $Q^{-\gamma}$. It is the step from the dual problem (3.4) to the closed forms of §3.2.
--
--   **Formalization Note** The page states the result at the optimal multiplier $\lambda^*$; here it is stated for every $\lambda$ with $\lambda\bar I^{\gamma}\le Q^{-\gamma}$, which is exactly the condition under which the printed formula gives $D^\lambda_0=0$, as admissibility (p. 8) requires. By Proposition 3.3, $\lambda^*$ satisfies it. The model is the static form of Problem 2.2, and $\hat\beta>0$ together with a positive leading coefficient of the $\alpha_+$-quadratic are standing hypotheses.
-- source:
--   Choi, Koo, Lim & Yoo, Endogenous Credit, Business Cycle, and Portfolio Selection, SSRN 2560607, https://ssrn.com/abstract=2560607 (version of October 25, 2023), p. 10, Proposition 3.1, D* clause; p. 8, (3.2)–(3.4)

import Mathlib
import Definitions.Def_EndoCredit_Baseline_Dual

open MeasureTheory
open scoped NNReal

namespace EndoCredit.Baseline

/-- Proposition 3.1, shadow-price clause: for a multiplier with `λ Ī^γ ≤ Q^{-γ}` (so that
`D_0 = 0`), the running-maximum process `D_t = max(0, max_{s≤t} Q^γ y_s - 1)` is an
admissible shadow price and minimizes the dual objective (3.4) over all admissible ones. -/
theorem proposition_3_1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : BrownianPath Ω) (hW : EthierKurtz.IsStandardBrownian P W)
    (p : Params) (hp : p.Standing) (lam : ℝ) (hlam : 0 < lam)
    (hlamI : lam * p.Ibar ^ p.gam ≤ ybar p) :
    Dlam p W lam ∈ AdmD p P W hW lam ∧
    IsLeast (dualObj p P W lam '' AdmD p P W hW lam) (dualObj p P W lam (Dlam p W lam)) := by sorry

end EndoCredit.Baseline
