-- Prove2me | Theorems.Thm_EmpiricalDRO_Consistency_lemma3_max_abs_little_o
-- name    : EmpiricalDRO.Consistency.lemma3_max_abs_little_o
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:06:28.430295+00:00
-- url     : https://prove2.me/theorems/ade871d4-89fe-4c06-b491-c7ba5a6b11fa
-- title:
--   Lemma 3, p. 38 — for i.i.d. Y_i with EY_i² < ∞, max_{1≤i≤n} |Y_i| = o(n^{1/2}) a.s.
-- statement:
--   Let $Y_1,Y_2,\dots$ be independent and identically distributed real random variables on a probability space $(\Omega,\mathcal F,P)$ with $\mathbb E[Y_1^2]<\infty$. Then, almost surely,
--   $$
--   \frac{\max_{1\le i\le n}|Y_i|}{\sqrt n}\longrightarrow 0\qquad(n\to\infty).
--   $$
--
--   This is Owen's Lemma 11.2, quoted as Lemma 3 by Lam. In the proof of Theorem 3 it is applied to the centred observations $\tilde h(x;\xi_i)=h(x;\xi_i)-Z_0(x)$: it ensures that $\max_i|\tilde h(x;\xi_i)|\le\lambda_n/2$ eventually for multipliers $\lambda_n$ growing like $n^{\varepsilon}$ with $1/2<\varepsilon<1$.
--
--   **Formalization Note** The sequence is indexed from $0$: $Y_1,\dots,Y_n$ are `Y 0, …, Y (n-1)`, and the maximum over the empty index set ($n=0$) is $0$. The same statement for nonnegative variables is the published, proved `NumStochOpt.ListScheduling.lemma_8_1_i_max_over_sqrt_ae`; applied to $|Y_i|$ it gives this one.
-- source:
--   Lam, Recovering Best Statistical Guarantees via the Empirical DRO, arXiv:1605.09349v1, p. 38, Lemma 3 (Owen (2001), Lemma 11.2)

import Mathlib
import Definitions.Def_EmpiricalDRO_Consistency_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace EmpiricalDRO.Consistency

/-- Lemma 3 (Owen (2001), Lemma 11.2), Lam, arXiv:1605.09349v1, p. 38: if `Y 0, Y 1, …` are i.i.d.
real random variables with `E Y² < ∞`, then `max_{i<n} |Y i| = o(n^{1/2})` almost surely. -/
theorem lemma3_max_abs_little_o {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (hY : ∀ i, Measurable (Y i))
    (hindep : iIndepFun Y P) (hident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    (h2 : Integrable (fun ω => Y 0 ω ^ 2) P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (⨆ i : Fin n, |Y i ω|) / Real.sqrt n) atTop (𝓝 0) := by sorry

end EmpiricalDRO.Consistency
