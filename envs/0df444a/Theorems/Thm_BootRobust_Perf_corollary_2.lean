-- Prove2me | Theorems.Thm_BootRobust_Perf_corollary_2
-- name    : BootRobust.Perf.corollary_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:41.40945+00:00
-- url     : https://prove2.me/theorems/dc48e20a-50da-497d-a42e-157b42cf76d4
-- title:
--   Corollary 2, p. 16 — the robust Nadaraya–Watson formulation (k = n) has bootstrap disappointment at most exp(−n·r)
-- statement:
--   Let $n\ge 1$, let $w>0$ be weights on the finite support $\Omega_n$, let $D_{\mathrm{tr}}\in\mathcal D_n$ have all entries positive, $r\in\mathbb R$, and let $L(z,\cdot)$ be a real loss for each decision $z$. Let $E_D[L(z,y)]=\sum_iw_iL(z,\bar y_i)D_i/\sum_iw_iD_i$ be the Nadaraya–Watson estimator and
--   $$c_n(z)=\sup\{E_D[L(z,y)]:\ D\in\mathcal D_n,\ B(D,D_{\mathrm{tr}})\le r\}$$
--   its robust budget with the bootstrap distance $B$. If $D_{\mathrm{bs}[n]}$ is the empirical distribution of $n$ independent draws from $D_{\mathrm{tr}}$, then for every decision $z$,
--   $$\mathbb P\big[E_{D_{\mathrm{bs}[n]}}[L(z,y)]>c_n(z)\big]\le\exp(-n\cdot r).$$
--
--   The bound is a single exponential with rate exactly $r$: a radius $r\ge\log(1/b)/n$ already gives bootstrap disappointment at most $b$.
--
--   **Formalization Note** With $k(n)=n$ the estimator (18) is the Nadaraya–Watson ratio (19) on every distribution, so the budget is (24) with $k=n$ (the $c_n$ of Corollary 1). The page states the bound for the robust prescriptor $z^r_{\mathrm{tr}[n]}(x_0)$; the proof fixes an arbitrary decision, and it is stated here for every $z$. Losses are real-valued (Assumption 1 allows $+\infty$); nonnegativity and convexity are not needed.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, Corollary 2, p. 16 (proof in B.6, p. 30)

import Mathlib
import Definitions.Def_BootRobust_Perf_Setting

namespace BootRobust.Perf

/-- Corollary 2, p. 16: the robust Nadaraya–Watson formulation (`k = n`) with the bootstrap
distance suffers bootstrap disappointment at most `exp(−n · r)`. -/
theorem corollary_2 {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (n : ℕ) (hn : 1 ≤ n) (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (Dtr : ι → ℝ) (hDtr : Dtr ∈ stdSimplex ℝ ι) (hDtrpos : ∀ i, 0 < Dtr i) (r : ℝ)
    {Z : Type*} (L : Z → ι → ℝ) (z : Z) :
    bootLaw Dtr n {ω | nwBudget w (L z) Dtr r < ((nwEst w (L z) (empDist ω) : ℝ) : EReal)} ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) * r))) := by sorry

end BootRobust.Perf
