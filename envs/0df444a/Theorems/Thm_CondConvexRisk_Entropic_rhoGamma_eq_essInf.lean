-- Prove2me | Theorems.Thm_CondConvexRisk_Entropic_rhoGamma_eq_essInf
-- name    : CondConvexRisk.Entropic.rhoGamma_eq_essInf
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:01:51.846601+00:00
-- url     : https://prove2.me/theorems/271ae93d-7c59-43c0-840a-16387d028895
-- title:
--   Section 5, p. 12 — $\rho_\gamma$ as capital requirement: ess.inf over $A_\gamma$
-- statement:
--   Let $\gamma>0$ and $X\in L^\infty$. Then, $P$-a.s.,
--   $$\frac1\gamma\log E_P(e^{-\gamma X}\mid\mathcal G)=\operatorname{ess.inf}\{Y\in L^\infty_{\mathcal G} : X+Y\in A_\gamma\}=\operatorname{ess.inf}\{Y\in L^\infty_{\mathcal G} : E_P(e^{-\gamma X}\mid\mathcal G)\le e^{\gamma Y}\},$$
--   where $A_\gamma=\{X\in L^\infty : E_P(e^{-\gamma X}\mid\mathcal G)\le1\}$.
--
--   This identifies the closed form of the conditional entropic risk measure with the capital-requirement definition $\rho_{A}(X)=\operatorname{ess.inf}\{Y\in L^\infty_{\mathcal G}: X+Y\in A\}$ of Proposition 2.5.
--
--   **Formalization Note** $L^\infty_{\mathcal G}$ is the set of `StronglyMeasurable[m]` functions with `MemLp ⊤`; the essential infimum is the predicate `IsEssInf` with values in `EReal`.
-- source:
--   Detlefsen & Scandolo, Conditional and Dynamic Convex Risk Measures, SFB 649 Discussion Paper 2005-006, p. 12, Section 5, display 'ργ(X) ≜ ess.inf {Y ∈ L∞_G | X + Y ∈ Aγ} = ess.inf {Y ∈ L∞_G | EP(e−γX | G) ≤ eγY} = 1/γ log EP(e−γX | G)'

import Mathlib
import Definitions.Def_CondConvexRisk_Entropic_Basic
import Definitions.Def_CondConvexRisk_Entropic_EntropicRisk

open MeasureTheory

namespace CondConvexRisk.Entropic

theorem rhoGamma_eq_essInf {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (γ : ℝ) (hγ : 0 < γ) (X : Ω → ℝ) (hX : MemLp X ⊤ P) :
    IsEssInf P
        (fun Y : {Y : Ω → ℝ // MemLp Y ⊤ P ∧ StronglyMeasurable[m] Y ∧
            X + Y ∈ acceptanceSet m P γ} => fun ω => ((Y.1 ω : ℝ) : EReal))
        (fun ω => ((rhoGamma m P γ X ω : ℝ) : EReal)) ∧
    IsEssInf P
        (fun Y : {Y : Ω → ℝ // MemLp Y ⊤ P ∧ StronglyMeasurable[m] Y ∧
            (P[fun x => Real.exp (-γ * X x) | m]) ≤ᵐ[P] fun ω => Real.exp (γ * Y ω)} =>
          fun ω => ((Y.1 ω : ℝ) : EReal))
        (fun ω => ((rhoGamma m P γ X ω : ℝ) : EReal)) := by sorry

end CondConvexRisk.Entropic
