-- Prove2me | Theorems.Thm_BootRobust_Perf_theorem_6
-- name    : BootRobust.Perf.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:55.926161+00:00
-- url     : https://prove2.me/theorems/4926498d-25fe-4ccb-ad18-df3c13d1f99c
-- title:
--   Theorem 6, p. 15 — the bootstrap disappointment of the entropic robust budget is at most Σⱼ exp(−n·max{r, r^j_n})
-- statement:
--   Let $\Omega_n$ be the finite support of the training data, $D_{\mathrm{tr}}\in\mathcal D_n$ its empirical distribution (all entries positive), $1\le k\le n$, $\emptyset=N^0\subseteq N^1\subseteq\dots\subseteq N^n=\Omega_n$ the nested neighbourhoods of the context, $w>0$ the weights, $r\in\mathbb R$ the robustness radius and $L(z,\cdot)$ a real loss for each decision $z$. Let
--
--   1. $E^n_D[L(z,y)|x=x_0]$ be the estimator (18): the $w$-weighted average of the loss over the smallest neighbourhood holding at least $k$ of the $n$ observations of $D$;
--   2. $\bar c_n(z)=\max_{j\in[n]}c^j_n(z)$ be the robust budget (26), where $c^j_n(z)=\sup\{E^{n,j}_D[L(z,y)|x=x_0]: D\in\mathcal D_n,\ B(D,D_{\mathrm{tr}})\le r\}$ and $B$ is the bootstrap distance (27);
--   3. $r^j_n=\inf\{B(D,D_{\mathrm{tr}}):D\in\mathcal D^j_n\}$ be the minimum radii (29);
--   4. $D_{\mathrm{bs}[n]}$ be the empirical distribution of $n$ independent draws from $D_{\mathrm{tr}}$ (14).
--
--   Then for every decision $z$ the bootstrap disappointment (17) satisfies
--   $$\mathbb P\Big[E^n_{D_{\mathrm{bs}[n]}}[L(z,y)|x=x_0]>\bar c_n(z)\Big]\ \le\ \sum_{j\in[n]}\exp\big(-n\cdot\max\{r,r^j_n\}\big),$$
--   with $\exp(-n\cdot(+\infty))=0$ when $\mathcal D^j_n$ is empty.
--
--   The theorem shows that the entropic robust budget is a bootstrap robust counterpart (Definition 1) of the nearest-neighbours-type estimator, with a disappointment decaying exponentially in $n$ at rate at least $r$.
--
--   **Formalization Note** The budget is the formulation (26), $\max_j c^j_n$, which the paper computes (Lemma 1) and which is never larger than (24); with it the theorem is the stronger statement. The page states the bound for the robust prescriptor $z^r_{\mathrm{tr}[n]}(x_0)$; the proof fixes an arbitrary decision, so it is stated for every $z$. $D_{\mathrm{tr}}$ is not required to lie in $\mathcal D_{n,n}$ and $r$ may be any real (both generalizations). Losses are real-valued (Assumption 1 allows $+\infty$); nonnegativity and convexity in $z$ are not used. Definition 2's neighbourhoods are abstracted to a nested chain, and covariates and distances do not appear.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, Theorem 6, p. 15

import Mathlib
import Definitions.Def_BootRobust_Perf_Setting

namespace BootRobust.Perf

/-- Theorem 6, p. 15: the robust formulation with bootstrap distance `B` and radius `r`
suffers bootstrap disappointment (17) at most `∑_{j ∈ [n]} exp(−n · max{r, r^j_n})`: for any
decision `z`, the probability that the estimate (18) on the bootstrap data exceeds the robust
budget (26) computed on the training data is at most that sum. -/
theorem theorem_6 {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n)
    (N : ℕ → Finset ι) (hNmono : Monotone N) (hN0 : N 0 = ∅) (hNn : N n = Finset.univ)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (Dtr : ι → ℝ) (hDtr : Dtr ∈ stdSimplex ℝ ι)
    (hDtrpos : ∀ i, 0 < Dtr i) (r : ℝ) {Z : Type*} (L : Z → ι → ℝ) (z : Z) :
    bootLaw Dtr n
        {ω | robustBudget n k N w (L z) Dtr r <
          ((nominalEst n k N w (L z) (empDist ω) : ℝ) : EReal)} ≤
      ∑ j ∈ Finset.Icc 1 n, expNeg n (max (r : EReal) (rj n k N Dtr j)) := by sorry

end BootRobust.Perf
