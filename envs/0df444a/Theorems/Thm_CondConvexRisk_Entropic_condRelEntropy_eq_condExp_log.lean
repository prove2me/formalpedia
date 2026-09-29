-- Prove2me | Theorems.Thm_CondConvexRisk_Entropic_condRelEntropy_eq_condExp_log
-- name    : CondConvexRisk.Entropic.condRelEntropy_eq_condExp_log
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:02:53.102646+00:00
-- url     : https://prove2.me/theorems/91c6bcbc-7327-4ca6-8211-e62e457297be
-- title:
--   Section 5, p. 13 — $H_{\mathcal G}(Q|P)=E_Q(\log dQ/dP\mid\mathcal G)$ for $Q\in\mathcal P_{\mathcal G}$
-- statement:
--   Let $Q\in\mathcal P_{\mathcal G}$ and $\varphi=dQ/dP$. Then $E_P(\varphi\mid\mathcal G)=1$ $P$-a.s. (it is the density of $Q$ w.r.t. $P$ on $\mathcal G$), and
--   $$H_{\mathcal G}(Q\mid P)=\frac{E_P(\varphi\log\varphi\mid\mathcal G)}{E_P(\varphi\mid\mathcal G)}=E_Q\big(\log\varphi\mid\mathcal G\big)\qquad P\text{-a.s.}$$
--
--   This representation expresses the conditional relative entropy as a conditional expectation under $Q$, which is the form used in the proof of Lemma 5.5.
--
--   **Formalization Note** Both conditional expectations are generalized ones with values in $[-\infty,+\infty]$ (positive part minus negative part, each a $[0,+\infty]$-valued conditional expectation); $\log0=0$ in Lean, which only matters on a $Q$-null set. The middle quotient is not stated separately: it equals the left side once $E_P(\varphi\mid\mathcal G)=1$.
-- source:
--   Detlefsen & Scandolo, Conditional and Dynamic Convex Risk Measures, SFB 649 Discussion Paper 2005-006, p. 13, Section 5, display after Definition 5.3 ('For Q ∈ PG, we have the representation …')

import Mathlib
import Definitions.Def_CondConvexRisk_Entropic_Basic
import Definitions.Def_CondConvexRisk_Entropic_EntropicRisk

open MeasureTheory

namespace CondConvexRisk.Entropic

theorem condRelEntropy_eq_condExp_log {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (Q : PG m P) :
    (P[density m P Q | m] =ᵐ[P] 1) ∧
      condRelEntropy m P Q =ᵐ[P] condExpExt m Q.1 (fun ω => Real.log (density m P Q ω)) := by sorry

end CondConvexRisk.Entropic
