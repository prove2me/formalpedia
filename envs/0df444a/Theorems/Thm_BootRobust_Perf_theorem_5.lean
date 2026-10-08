-- Prove2me | Theorems.Thm_BootRobust_Perf_theorem_5
-- name    : BootRobust.Perf.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:08.633306+00:00
-- url     : https://prove2.me/theorems/efa3ad78-3482-480f-90a1-a85f3df98df8
-- title:
--   Theorem 5 (Csiszár 1984), p. 14 — P(D_bs[n] ∈ C) ≤ exp(−n · inf_{D∈C} B(D, D_tr[n])) for every convex C ⊆ Dₙ
-- statement:
--   Let $D_{\mathrm{tr}}$ be a distribution on the finite set $\Omega_n$ with $D_{\mathrm{tr},i}>0$ for all $i$, let $n\ge 1$, and let $D_{\mathrm{bs}[n]}$ be the empirical distribution of $n$ independent draws from $D_{\mathrm{tr}}$. For every convex set $\mathcal C\subseteq\mathcal D_n$,
--   $$\mathbb P\big[D_{\mathrm{bs}[n]}\in\mathcal C\big]\le\exp\Big(-n\cdot\inf_{D\in\mathcal C}B(D,D_{\mathrm{tr}})\Big),$$
--   where $B(D,D')=\sum_iD_i\log(D_i/D'_i)$ is the relative entropy and $\exp(-n\cdot(+\infty))=0$ (the case $\mathcal C=\emptyset$).
--
--   This finite-sample large-deviation bound, without a polynomial prefactor, is Csiszár's inequality (Ann. Probab. 1984, Theorem 1). It is the probabilistic core of Theorem 6 and Corollary 2.
--
--   **Formalization Note** The bootstrap law is the $n$-fold product of $\sum_iD_{\mathrm{tr},i}\delta_i$ on a measurable space with measurable singletons. No closedness or openness of $\mathcal C$ is assumed.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, Theorem 5 and (28), p. 14 (citing Csiszár 1984, Theorem 1)

import Mathlib
import Definitions.Def_BootRobust_Perf_Setting

namespace BootRobust.Perf

/-- Theorem 5 (Csiszár 1984, Theorem 1), p. 14: the probability that the empirical
distribution of `n` i.i.d. draws from `D_tr` lies in a convex set `C ⊆ Dₙ` is at most
`exp(−n · inf_{D ∈ C} B(D, D_tr))`. -/
theorem theorem_5 {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (Dtr : ι → ℝ) (hDtr : Dtr ∈ stdSimplex ℝ ι)
    (hDtrpos : ∀ i, 0 < Dtr i) (n : ℕ) (hn : 1 ≤ n) (C : Set (ι → ℝ)) (hC : Convex ℝ C)
    (hCsub : C ⊆ stdSimplex ℝ ι) :
    bootLaw Dtr n {ω | empDist ω ∈ C} ≤ expNeg n (⨅ D ∈ C, bootDist D Dtr) := by sorry

end BootRobust.Perf
