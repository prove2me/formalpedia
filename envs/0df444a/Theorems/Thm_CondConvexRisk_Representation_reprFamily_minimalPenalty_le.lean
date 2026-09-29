-- Prove2me | Theorems.Thm_CondConvexRisk_Representation_reprFamily_minimalPenalty_le
-- name    : CondConvexRisk.Representation.reprFamily_minimalPenalty_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:55:22.384919+00:00
-- url     : https://prove2.me/theorems/fbd8c441-4cd9-4b8f-949d-9986946ab035
-- title:
--   Proof of Theorem 3.2 ($a\Rightarrow c$), first step — $\rho(X)\ge\operatorname{ess.sup}_Q\{-E_Q(X|\mathcal G)-\alpha^*(Q)\}$
-- statement:
--   Let $\rho:L^\infty\to L^\infty_{\mathcal G}$ be a conditional convex risk measure and $\alpha^*$ its minimal penalty,
--   $\alpha^*(Q)=\operatorname{ess.sup}_{X\in L^\infty}\{-E_Q(X\mid\mathcal G)-\rho(X)\}$ for $Q\in\mathcal P_{\mathcal G}$. Then for every $X\in L^\infty$:
--   1. $\rho(X)\ge -E_Q(X\mid\mathcal G)-\alpha^*(Q)$ $P$-a.s. for every $Q\in\mathcal P_{\mathcal G}$;
--   2. consequently
--   $$\rho(X)\ge\operatorname*{ess.sup}_{Q\in\mathcal P_{\mathcal G}}\{-E_Q(X\mid\mathcal G)-\alpha^*(Q)\}\quad P\text{-a.s.}$$
--
--   This is the easy half of the representation with the minimal penalty.
--
--   **Formalization Note** Part 2 is stated for every essential supremum $W$ of the family; the expression $-E_Q(X\mid\mathcal G)-\alpha^*(Q)$ is computed in `EReal` with $\alpha^*(Q)\in[0,+\infty]$.
-- source:
--   Detlefsen & Scandolo, Conditional and Dynamic Convex Risk Measures, SFB 649 Discussion Paper 2005-006, p. 6, proof of Theorem 3.2, step a ⇒ c (first inequality)

import Mathlib
import Definitions.Def_CondConvexRisk_Representation_EssSup
import Definitions.Def_CondConvexRisk_Representation_CondConvexRiskMeasure
import Definitions.Def_CondConvexRisk_Representation_Representable

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

theorem reprFamily_minimalPenalty_le {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (ρ : (Ω → ℝ) → Ω → ℝ) (hρ : IsCondConvexRiskMeasure m P ρ)
    (α : PG m P → Ω → ENNReal) (hα : IsMinimalPenalty m P ρ α)
    (X : Ω → ℝ) (hX : MemLp X ⊤ P) :
    (∀ Q : PG m P, reprFamily m P α X Q ≤ᵐ[P] fun ω => (ρ X ω : EReal)) ∧
    ∀ W : Ω → EReal, IsEssSup P (reprFamily m P α X) W →
      W ≤ᵐ[P] fun ω => (ρ X ω : EReal) := by sorry

end CondConvexRisk.Representation
