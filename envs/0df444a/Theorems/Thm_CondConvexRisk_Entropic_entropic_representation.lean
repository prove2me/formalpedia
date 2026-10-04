-- Prove2me | Theorems.Thm_CondConvexRisk_Entropic_entropic_representation
-- name    : CondConvexRisk.Entropic.entropic_representation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:04:47.707285+00:00
-- url     : https://prove2.me/theorems/f78aaacc-b239-4b56-9b37-79fe2f2992f7
-- title:
--   Proposition 5.4 — robust representation of $\rho_\gamma$ with minimal penalty $\frac1\gamma H_{\mathcal G}(Q|P)$
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $\mathcal G\subseteq\mathcal F$ a sub-$\sigma$-algebra, $\gamma>0$, and let $\rho_\gamma(X)=\frac1\gamma\log E_P(e^{-\gamma X}\mid\mathcal G)$ be the conditional entropic risk measure. Then:
--
--   1. $\rho_\gamma$ is representable with penalty $\frac1\gamma H_{\mathcal G}(\cdot\mid P)$: for every $X\in L^\infty$,
--   $$\rho_\gamma(X)=\operatorname{ess.sup}_{Q\in\mathcal P_{\mathcal G}}\Big\{-E_Q(X\mid\mathcal G)-\frac1\gamma H_{\mathcal G}(Q\mid P)\Big\}\qquad P\text{-a.s.};$$
--   2. its minimal penalty function is
--   $$\alpha^*(Q)=\operatorname{ess.sup}_{X\in L^\infty}\{-E_Q(X\mid\mathcal G)-\rho_\gamma(X)\}=\frac1\gamma H_{\mathcal G}(Q\mid P),\qquad Q\in\mathcal P_{\mathcal G}.$$
--
--   This is the conditional analogue of the classical fact that the entropic risk measure has relative entropy (scaled by $1/\gamma$) as its penalty, and it explains the name "entropic".
--
--   **Formalization Note** Part 1 is stated with the minimal penalty as the penalty (what the paper obtains through Theorem 3.2 (c)), not with an unspecified penalty. Essential suprema are the predicates `IsEssSup` in `EReal`; $-E_Q(X\mid\mathcal G)-(+\infty)=-\infty$. $H_{\mathcal G}$ is the $[-\infty,+\infty]$-valued generalized conditional expectation of $\varphi\log\varphi$ (see the definition item), so the case $H_{\mathcal G}=+\infty$ is not collapsed to $0$.
-- source:
--   Detlefsen & Scandolo, Conditional and Dynamic Convex Risk Measures, SFB 649 Discussion Paper 2005-006, p. 13, Proposition 5.4

import Mathlib
import Definitions.Def_CondConvexRisk_Entropic_Basic
import Definitions.Def_CondConvexRisk_Entropic_EntropicRisk

open MeasureTheory

namespace CondConvexRisk.Entropic

theorem entropic_representation {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (γ : ℝ) (hγ : 0 < γ) :
    (∀ X : Ω → ℝ, MemLp X ⊤ P →
      IsEssSup P (entropicReprFamily m P γ X) (fun ω => ((rhoGamma m P γ X ω : ℝ) : EReal))) ∧
    IsMinimalPenalty m P (rhoGamma m P γ)
      (fun Q ω => ((γ⁻¹ : ℝ) : EReal) * condRelEntropy m P Q ω) := by sorry

end CondConvexRisk.Entropic
