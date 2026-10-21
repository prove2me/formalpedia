-- Prove2me | Theorems.Thm_EndoCredit_Baseline_theorem_3_1
-- name    : EndoCredit.Baseline.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:24.637975+00:00
-- url     : https://prove2.me/theorems/1462df92-d610-4b0b-9113-dbd903192e42
-- title:
--   Theorem 3.1, p. 9 — duality V(x, Ī) = min over λ > 0 of J(λ, Ī) + λx, and c* from (3.3) is optimal
-- statement:
--   Consider the baseline limited-commitment problem in its static form, with initial income $\bar I>0$ and initial wealth $x\ge-m^*\bar I$. Write $V(x,\bar I)$ for the maximal expected utility $\mathbb E\int_0^\infty e^{-\beta t}u(c_t)\,dt$ over consumption plans that meet the budget $\mathbb E\int_0^\infty H_t(c_t-I_t)\,dt\le x$ and every participation constraint (2.6). Then:
--
--   1. The maximum $V(x,\bar I)$ is attained and satisfies the convex duality relation (3.5),
--   $$V(x,\bar I)=\min_{\lambda>0}\big\{J(\lambda,\bar I)+\lambda x\big\},$$
--   where $J(\lambda,\bar I)$ is the minimum over admissible shadow-price processes $D$ of the dual objective (3.4); the minimum over $\lambda$ and $D$ is attained.
--   2. If $\lambda^*>0$ and an admissible $D^*$ jointly minimize the dual objective plus $\lambda x$, then the consumption $c^*_t=(u')^{-1}(\lambda^*e^{\beta t}H_t/(1+D^*_t))$ of (3.3) is feasible and optimal.
--
--   The duality theorem converts the infinitely many participation constraints into a single shadow-price process and is the bridge from the dual stopping problems of §3.1 to the closed forms of §3.2.
--
--   **Formalization Note** The theorem is posed for $x\ge-m^*\bar I$; below that level the feasible set is empty (Proposition 3.2) and $V=-\infty$ in the paper's convention, which is not stated here. $J(\lambda,\bar I)$ is never defined as a real infimum: "$\min_{\lambda>0}\{J+\lambda x\}$" is the least element of the set of all values $\text{dual objective}(\lambda,D)+\lambda x$, and "$\lambda^*=\arg\min$, $D=D^*$" is a pair at which that least element is attained. Problem 2.2 is posed in its static form (§3's Lagrangian (3.1)); $\hat\beta>0$ and a positive leading coefficient of the $\alpha_+$-quadratic are standing hypotheses.
-- source:
--   Choi, Koo, Lim & Yoo, Endogenous Credit, Business Cycle, and Portfolio Selection, SSRN 2560607, https://ssrn.com/abstract=2560607 (version of October 25, 2023), p. 9, Theorem 3.1, (3.5); p. 8, (3.1)–(3.4)

import Mathlib
import Definitions.Def_EndoCredit_Baseline_Dual

open MeasureTheory
open scoped NNReal

namespace EndoCredit.Baseline

/-- Theorem 3.1 (duality) for initial wealth above the credit limit: the primal value
`V(x, Ī)` is attained and equals `min_{λ>0} min_D {dualObj λ D + λx}`; and the consumption
(3.3) built from any minimizing pair `(λ*, D*)` is feasible and optimal. -/
theorem theorem_3_1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : BrownianPath Ω) (hW : EthierKurtz.IsStandardBrownian P W)
    (p : Params) (hp : p.Standing) (x : ℝ) (hx : -(mStar p) * p.Ibar ≤ x) :
    (∃ V : ℝ, IsGreatest (J0 p P '' Feasible p P W hW x) V ∧
      IsLeast (dualValues p P W hW x) V) ∧
    ∀ lam : ℝ, 0 < lam → ∀ D ∈ AdmD p P W hW lam,
      dualObj p P W lam D + lam * x ∈ lowerBounds (dualValues p P W hW x) →
      cOf p W lam D ∈ Feasible p P W hW x ∧
      IsGreatest (J0 p P '' Feasible p P W hW x) (J0 p P (cOf p W lam D)) := by sorry

end EndoCredit.Baseline
