-- Prove2me | Theorems.Thm_CondConvexRisk_Representation_expectation_essSup_eq_iSup
-- name    : CondConvexRisk.Representation.expectation_essSup_eq_iSup
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:54:42.747053+00:00
-- url     : https://prove2.me/theorems/b37af577-1f90-47ba-97ab-7117d358b316
-- title:
--   Lemma A.2 — expectation of the essential supremum of a directed family
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $\mathcal X=\{X_i\}_{i\in I}$ an upward directed family of extended random variables whose expectations exist, and assume some member $X_{i_0}$ has $E_P[X_{i_0}^-]<\infty$. Then the expectation of $\operatorname{ess.sup}\mathcal X$ exists and
--   $$E_P\big(\operatorname{ess.sup}\mathcal X\big)=\sup_{i\in I}E_P X_i .$$
--
--   This lemma lets one exchange expectation and essential supremum; in the proof of Theorem 3.2 it identifies $E_P[\alpha^*(Q)]$ with the unconditional penalty $\alpha^*_0(Q)$.
--
--   **Formalization Note** The paper's proviso "provided the expectations exist" is made precise as: every member has an expectation in $[-\infty,+\infty]$ and one member has integrable negative part. Without the latter the identity fails (take $g\ge0$ with $E[g\,1_{\{g>n\}}]=\infty$ for all $n$ and $X_n=-g\,1_{\{g>n\}}\nearrow0$: every $E X_n=-\infty$ while the essential supremum is $0$). In the paper's application the member $X=0$ of $B_Q$ is $0$.
-- source:
--   Detlefsen & Scandolo, Conditional and Dynamic Convex Risk Measures, SFB 649 Discussion Paper 2005-006, pp. 19–20, Lemma A.2

import Mathlib
import Definitions.Def_CondConvexRisk_Representation_EssSup

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

theorem expectation_essSup_eq_iSup {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : ι → Ω → EReal) (hF : ∀ i, AEMeasurable (F i) P)
    (hdir : IsUpwardDirected P F) (hexp : ∀ i, HasExpectation P (F i))
    (i₀ : ι) (hi₀ : negExpectation P (F i₀) ≠ ⊤)
    (Z : Ω → EReal) (hZ : IsEssSup P F Z) :
    HasExpectation P Z ∧ expectation P Z = ⨆ i, expectation P (F i) := by sorry

end CondConvexRisk.Representation
