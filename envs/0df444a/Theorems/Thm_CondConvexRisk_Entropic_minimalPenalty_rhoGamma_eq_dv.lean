-- Prove2me | Theorems.Thm_CondConvexRisk_Entropic_minimalPenalty_rhoGamma_eq_dv
-- name    : CondConvexRisk.Entropic.minimalPenalty_rhoGamma_eq_dv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:03:39.635187+00:00
-- url     : https://prove2.me/theorems/f631258b-ee66-435b-a4b6-9352b8cde9a9
-- title:
--   Proof of Proposition 5.4, p. 13 — $\alpha^*(Q)=\frac1\gamma\,\mathrm{ess.sup}_Z\{E_Q(Z|\mathcal G)-\log E_P(e^Z|\mathcal G)\}$
-- statement:
--   Let $\gamma>0$ and $Q\in\mathcal P_{\mathcal G}$. For the conditional entropic risk measure $\rho_\gamma$,
--   $$\alpha^*(Q)=\operatorname{ess.sup}_{X\in L^\infty}\Big\{-E_Q(X\mid\mathcal G)-\frac1\gamma\log E_P(e^{-\gamma X}\mid\mathcal G)\Big\}=\frac1\gamma\operatorname{ess.sup}_{Z\in L^\infty}\big\{E_Q(Z\mid\mathcal G)-\log E_P(e^{Z}\mid\mathcal G)\big\}.$$
--   Precisely: a random variable $V$ is the essential supremum of $\{E_Q(Z\mid\mathcal G)-\log E_P(e^Z\mid\mathcal G)\}_{Z\in L^\infty}$ if and only if $\frac1\gamma V$ is the essential supremum of $\{-E_Q(X\mid\mathcal G)-\rho_\gamma(X)\}_{X\in L^\infty}$.
--
--   This reduces the minimal penalty of $\rho_\gamma$ to the conditional Donsker–Varadhan functional of Lemma 5.5.
--
--   **Formalization Note** Essential suprema are the predicate `IsEssSup` with values in `EReal`; the "if and only if" form states the equality of the two essential suprema without choosing representatives.
-- source:
--   Detlefsen & Scandolo, Conditional and Dynamic Convex Risk Measures, SFB 649 Discussion Paper 2005-006, p. 13, Proof of Proposition 5.4 (display computing α*(Q))

import Mathlib
import Definitions.Def_CondConvexRisk_Entropic_Basic
import Definitions.Def_CondConvexRisk_Entropic_EntropicRisk

open MeasureTheory

namespace CondConvexRisk.Entropic

theorem minimalPenalty_rhoGamma_eq_dv {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (γ : ℝ) (hγ : 0 < γ) (Q : PG m P) (V : Ω → EReal) :
    IsEssSup P (dvFamily m P Q) V ↔
      IsEssSup P (penaltyFamily m P (rhoGamma m P γ) Q) (fun ω => ((γ⁻¹ : ℝ) : EReal) * V ω) := by sorry

end CondConvexRisk.Entropic
