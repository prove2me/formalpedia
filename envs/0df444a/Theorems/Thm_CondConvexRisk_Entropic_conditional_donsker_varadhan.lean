-- Prove2me | Theorems.Thm_CondConvexRisk_Entropic_conditional_donsker_varadhan
-- name    : CondConvexRisk.Entropic.conditional_donsker_varadhan
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:04:14.204505+00:00
-- url     : https://prove2.me/theorems/8de65162-ffde-437d-9478-ae452329a5a5
-- title:
--   Lemma 5.5 — conditional Donsker–Varadhan variational formula
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $\mathcal G\subseteq\mathcal F$ a sub-$\sigma$-algebra and $Q\in\mathcal P_{\mathcal G}$ ($Q\ll P$, $Q=P$ on $\mathcal G$). Then, $P$-a.s.,
--   $$\operatorname{ess.sup}_{Z\in L^\infty}\Big\{E_Q(Z\mid\mathcal G)-\log E_P\big(e^{Z}\mid\mathcal G\big)\Big\}=H_{\mathcal G}(Q\mid P),$$
--   where $H_{\mathcal G}(Q\mid P)=E_P(\varphi\log\varphi\mid\mathcal G)\in[0,+\infty]$, $\varphi=dQ/dP$.
--
--   This is the conditional version of the variational (Donsker–Varadhan) characterization of relative entropy, and it identifies the minimal penalty of the conditional entropic risk measure.
--
--   **Formalization Note** The essential supremum is the predicate `IsEssSup` in `EReal`; $H_{\mathcal G}$ may equal $+\infty$ on a set of positive probability, and the statement covers that case.
-- source:
--   Detlefsen & Scandolo, Conditional and Dynamic Convex Risk Measures, SFB 649 Discussion Paper 2005-006, p. 13, Lemma 5.5 (proof pp. 13–14)

import Mathlib
import Definitions.Def_CondConvexRisk_Entropic_Basic
import Definitions.Def_CondConvexRisk_Entropic_EntropicRisk

open MeasureTheory

namespace CondConvexRisk.Entropic

theorem conditional_donsker_varadhan {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (Q : PG m P) :
    IsEssSup P (dvFamily m P Q) (condRelEntropy m P Q) := by sorry

end CondConvexRisk.Entropic
