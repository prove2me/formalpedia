-- Prove2me | Theorems.Thm_EmpiricalDRO_Coverage_lemma3_max_abs_little_o
-- name    : EmpiricalDRO.Coverage.lemma3_max_abs_little_o
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:08:27.578008+00:00
-- url     : https://prove2.me/theorems/daabacd1-3c90-41c7-a62e-4b7040531cea
-- title:
--   Lemma 3, p. 38 — for i.i.d. Y_i with E Y_i² < ∞, max_{1≤i≤n} |Y_i| = o(n^{1/2}) a.s.
-- statement:
--   Let $Y_1,Y_2,\dots$ be independent, identically distributed real random variables on a probability space $(\Omega,\mathcal F,P)$ with $\mathbb E\,Y_1^2<\infty$. Then, almost surely,
--   $$
--   \lim_{n\to\infty}\frac{\max_{1\le i\le n}|Y_i|}{\sqrt n}=0,
--   $$
--   that is, $\max_{1\le i\le n}|Y_i|=o(n^{1/2})$ almost surely.
--
--   In the proof of the empirical likelihood theorem this controls the largest centred observation $\max_i|h(x;\xi_i)-Z_0(x)|$, so that the multiplier of the optimal weights is $O_p(n^{-1/2})$ and the Taylor remainder of $\log(1+\lambda\tilde h_i)$ is negligible.
--
--   **Formalization Note.** The sequence is indexed from $0$, and the maximum over $1\le i\le n$ is the supremum over the first $n$ indices (the supremum of the empty family is $0$ at $n=0$). Independence is mutual independence of the sequence. The published theorem `NumStochOpt.ListScheduling.lemma_8_1_i_max_over_sqrt_ae` (Proved) is the same statement for nonnegative variables; applied to $|Y_i|$ it gives this lemma.
-- source:
--   Lam, Recovering Best Statistical Guarantees via the Empirical DRO, arXiv:1605.09349v1, p. 38, Lemma 3 (Owen (2001), Lemma 11.2)

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology

namespace EmpiricalDRO.Coverage

/-- Lemma 3 (Owen (2001), Lemma 11.2), Lam, arXiv:1605.09349v1, p. 38: for i.i.d. real `Y 0, Y 1, …`
with `E Y² < ∞`, `max_{i < n} |Y i| = o(n^{1/2})` almost surely. -/
theorem lemma3_max_abs_little_o {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (hY : ∀ i, Measurable (Y i))
    (hindep : iIndepFun Y P) (hident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    (h2 : Integrable (fun ω => Y 0 ω ^ 2) P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (⨆ i : Fin n, |Y i ω|) / Real.sqrt n) atTop (𝓝 0) := by sorry

end EmpiricalDRO.Coverage
