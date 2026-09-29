-- Prove2me | Theorems.Thm_CondConvexRisk_Representation_penaltyFamily_upwardDirected
-- name    : CondConvexRisk.Representation.penaltyFamily_upwardDirected
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:57:13.275253+00:00
-- url     : https://prove2.me/theorems/60c3df5a-a637-4b35-be73-7bb5fa229cf2
-- title:
--   Proof of Theorem 3.2 — the family $B_Q$ is upward directed
-- statement:
--   Let $\rho:L^\infty\to L^\infty_{\mathcal G}$ be a conditional convex risk measure and $Q\in\mathcal P_{\mathcal G}$. Then the family
--   $$B_Q=\{-E_Q(X\mid\mathcal G)-\rho(X) : X\in L^\infty\}$$
--   is upward directed: for all $X,Y\in L^\infty$ there is $Z\in L^\infty$ with
--   $$-E_Q(Z\mid\mathcal G)-\rho(Z)\ge\max\big(-E_Q(X\mid\mathcal G)-\rho(X),\,-E_Q(Y\mid\mathcal G)-\rho(Y)\big)\quad P\text{-a.s.}$$
--
--   Directedness is what allows Lemma A.2 to exchange $E_P$ with the essential supremum defining $\alpha^*(Q)$.
-- source:
--   Detlefsen & Scandolo, Conditional and Dynamic Convex Risk Measures, SFB 649 Discussion Paper 2005-006, p. 7, proof of Theorem 3.2 (claim that B_Q is upward directed)

import Mathlib
import Definitions.Def_CondConvexRisk_Representation_EssSup
import Definitions.Def_CondConvexRisk_Representation_CondConvexRiskMeasure
import Definitions.Def_CondConvexRisk_Representation_Representable

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

theorem penaltyFamily_upwardDirected {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (ρ : (Ω → ℝ) → Ω → ℝ) (hρ : IsCondConvexRiskMeasure m P ρ) (Q : PG m P) :
    IsUpwardDirected P (penaltyFamily m P ρ Q) := by sorry

end CondConvexRisk.Representation
