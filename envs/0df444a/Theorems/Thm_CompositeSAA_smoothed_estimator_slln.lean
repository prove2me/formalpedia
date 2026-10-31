-- Prove2me | Theorems.Thm_CompositeSAA_smoothed_estimator_slln
-- name    : CompositeSAA.smoothed_estimator_slln
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:36:31.869761+00:00
-- url     : https://prove2.me/theorems/be792c9a-6b7e-459b-8480-627204a673d3
-- title:
--   Theorem 7 — strong law of large numbers for mixed smoothed composite estimators (corrected: nonempty estimator solution sets, smoothing stays in $\operatorname{conv}\mathcal X$)
-- statement:
--   Assume the standing assumptions on problem (3). Let $X_1,X_2,\dots$ be independent random vectors with law $P$ and $\mathbb E\|X\|<\infty$, let $J\subseteq\{1,\dots,k+1\}$ be the set of smoothed levels, and let the smoothing measures $\mu_N$ satisfy Assumption 6. Assume:
--
--   1. for $j\in J$, every component $f_{j,i}(u,\eta_j,\cdot)$, $i=1,\dots,m_{j-1}$, admits the modulus of continuity $w_{j,i}$ on $\operatorname{conv}(\mathcal X)$ for all $(u,\eta_j)\in\mathcal U\times I_j$ (the class $\tilde{\mathfrak F}$); if $k+1\in J$, every $f_{k+1,i}(u,\cdot)$ admits a modulus $w_{k+1,i}$ for all $u\in\mathcal U$;
--   2. for $j\notin J$, $\|f_j(u,\eta_j,x)\|\le g(x)$, and if $k+1\notin J$, $\|f_{k+1}(u,x)\|\le g(x)$, for all $(u,\eta)\in\mathcal U\times I$ and $x\in\mathcal X$, where $g$ is $P$-integrable;
--   3. if $J\ne\emptyset$, the smoothing does not leave $\operatorname{conv}(\mathcal X)$: for all $N$ large enough, $x+z\in\operatorname{conv}(\mathcal X)$ for $P$-almost every $x$ and $\mu_N$-almost every $z$;
--   4. almost surely, for all $N$ large enough the estimated problem has a nonempty solution set $S^{(N,J)}_\mu\subseteq\mathcal U$ (Assumption 2).
--
--   Then, almost surely,
--
--   $$
--   \varrho^{(N,J)}_\mu[u,X]\to\varrho[u,X]\ \ \forall u\in\mathcal U,\qquad\vartheta^{(N,J)}_\mu\to\vartheta,\qquad\mathsf d(S^{(N,J)}_\mu,S)\to0,
--   $$
--
--   and if problem (3) has a unique solution, then also $\mathsf D(S^{(N,J)}_\mu,S)\to0$.
--
--   The theorem lets one smooth any subset of the levels of a composite functional, for instance with a kernel $d\mu_N(z)=h_N^{-m}K(z/h_N)\,dz$, and still obtain strongly consistent optimal values and solutions; the empirical estimator is the case $J=\emptyset$.
--
--   Differences from the source:
--   - correction: added hypothesis 4, Assumption 2 with nonemptiness, almost surely; reason: the theorem does not cite Assumption 2, but its proof ("in the same way as in Theorem 3") needs it, and without nonemptiness the theorem is false: for $X\sim N(0,1)$, $f_1(u,\eta,x)=u^2/(1+u^2)+ux$, $f_2=0$, $U=\mathbb R$, $\mathcal U=I_1=[-1,1]$, $J=\{1\}$ and $\mu_N=N(0,1/N)$, every hypothesis 1–3 holds (modulus $w(t)=t$, $\mathcal X=\mathbb R$), but the estimated objective $u^2/(1+u^2)+u\bar X_N$ has no minimum almost surely.
--   - correction: no condition linking $\mu_N$ and $\mathcal X$ → hypothesis 3 (only when $J\ne\emptyset$); reason: the proof applies Theorem 4 to $P_N*\mu_N$, which needs $P_N*\mu_N$ concentrated where the moduli hold, and without it the theorem is false: take $P=\delta_0$, $\mathcal X=\{0\}$, $U=\mathcal U=I_1=[-1,1]$, $f_2=0$, $f_1(u,\eta,x)=u^2+u\,\mathbf 1[x\ne0]$, $J=\{1\}$ and $\mu_N$ uniform on $[-1/N,1/N]$; hypotheses 1, 2, 4 and the standing assumptions hold ($\operatorname{conv}(\mathcal X)=\{0\}$, $S=\{0\}$, $S_N=\{-\tfrac12\}$), but the estimator is $u^2+u$ and $\vartheta_N=-\tfrac14\not\to\vartheta=0$. Taking $\mathcal X=\mathbb R^m$ always satisfies hypothesis 3.
--   - encoding: the printed "Assumption 2" → Assumption 6 of p.9; reason: label slip in the cross-reference.
--   - reading: "$f_{k+1,i}(u,\cdot)\in\tilde{\mathfrak F}$ for all $u\in U$" → for all $u\in\mathcal U$; reason: $\tilde{\mathfrak F}$ ranges over $u\in\mathcal U$ (p.5), and the $\mathcal U$ reading is the weaker hypothesis.
--   - reading: "uniformly bounded by a $P$-integrable function $g$" → $\|f_j(u,\eta,x)\|\le g(x)$ for $x\in\mathcal X$, as in Proposition 5; reason: the weaker of the two readings.
--   - reading: "$\{\mu_N\}$ independent of $P_N$" → a deterministic sequence; the inner $\lim_{N\to\infty}$ of Assumption 6 → $\limsup$; reason: the only randomness of the paper is the sample, and the printed limit presupposes existence; the limsup reading is the weaker hypothesis.
--   - generalization: finite $p$-th moment of $X$, $p\ge1$ → $\mathbb E\|X\|<\infty$; reason: the case $p=1$ covers every $p\ge1$.
--   - generalization: the §3.2 preamble "assume that the functions $f_j$ … belong to the set $\tilde{\mathfrak F}$" → required only for $j\in J$; reason: the theorem's own bullets require it only there, and the unsmoothed levels are handled by the envelope $g$.
--   - generalization: "without loss of generality $\mathcal U$ and $I_j$ are convex" → not assumed; reason: convex sets are an instance.
--   - generalization: "for every $u\in\mathcal U$, almost surely" → "almost surely, for every $u\in\mathcal U$"; reason: implies the printed order.
--   - generalization: the integrals in (13) are presupposed to exist for every $u\in U$, $\eta$ and $N$ → no such presupposition (a non-existent integral takes Lean's value $0$); reason: the hypotheses make them exist on $\mathcal U\times I_j$, where the estimator converges, and where the paper's integrals exist the Lean estimator is the paper's.
--   - encoding: i.i.d. sample as mutually independent `X i` each with law $P$, 0-based; the moduli of $\tilde{\mathfrak F}$ indexed by level and component; $\mathbb R^d$, $\mathsf d$, $\mathsf D$, $S$, $\vartheta$ as in Theorem 3; reason: Lean convention, same instances.
-- source:
--   Dentcheva, Lin, Penev, arXiv:2201.01338v1, Theorem 7, p.10 (with Assumption 2, p.6, Assumption 6, p.9, displays (12)–(13), pp.9–10)

import Mathlib
import Definitions.Def_CompositeSAA_CompositeModel
import Definitions.Def_CompositeSAA_mixedEstimator
import Definitions.Def_CompositeSAA_riskFunctional
import Definitions.Def_CompositeSAA_optimalValue
import Definitions.Def_CompositeSAA_solutionSet
import Definitions.Def_CompositeSAA_excess
import Definitions.Def_CompositeSAA_StandingAssumptions
import Definitions.Def_CompositeSAA_IsModulus
import Definitions.Def_CompositeSAA_SmoothingAssumption

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace CompositeSAA

/-- Dentcheva, Lin, Penev, arXiv:2201.01338v1, Theorem 7, p.10 (corrected): the strong law of
large numbers for the mixed smoothed/empirical composite estimator `ϱ^{(N,J)}_µ`.

Under the standing assumptions, let `X_1, X_2, …` be i.i.d. with law `P` and `E‖X‖ < ∞`, let
`J ⊆ {1, …, k + 1}`, and let `(µ_N)` satisfy Assumption 6. Assume

* for `j ∈ J`, every component `f_{j,i}(u, η_j, ·)` (`i = 1, …, m_{j−1}`) admits the modulus of
  continuity `w_{j,i}` on `conv(𝒳)` for all `(u, η_j) ∈ 𝒰 × I_j` (the class `𝔉̃`); if
  `k + 1 ∈ J`, every `f_{k+1,i}(u, ·)` admits `wLast_i` for all `u ∈ 𝒰`;
* for `j ∉ J`, `‖f_j(u, η_j, x)‖ ≤ g(x)` and, if `k + 1 ∉ J`, `‖f_{k+1}(u, x)‖ ≤ g(x)` for all
  `(u, η) ∈ 𝒰 × I` and `x ∈ 𝒳`, with `g` `P`-integrable;
* if `J ≠ ∅`, the smoothed sample stays in `conv(𝒳)`: for all `N` large enough,
  `x + z ∈ conv(𝒳)` for `P`-a.e. `x` and `µ_N`-a.e. `z`;
* almost surely, for `N` large, `S^{(N,J)}_µ ≠ ∅` and `S^{(N,J)}_µ ⊆ 𝒰` (Assumption 2).

Then, almost surely: `ϱ^{(N,J)}_µ[u] → ϱ[u]` for every `u ∈ 𝒰`, `ϑ^{(N,J)}_µ → ϑ`,
`d(S^{(N,J)}_µ, S) → 0`, and, if problem (3) has a unique solution `û`, `D(S^{(N,J)}_µ, S) → 0`.

**Formalization Note**
1. The sample is `X : ℕ → Ω → ℝ^{mX}`, mutually independent with law `P`; the paper's
   `X_1, …, X_N` are `X 0, …, X (N − 1)`. The `µ_N` are deterministic.
2. Correction (nonemptiness): the theorem does not cite Assumption 2, but its proof ("in the same
   way as in Theorem 3") needs it, and with nonemptiness, since without it the theorem is false.
3. Correction (smoothing stays in `conv(𝒳)`, only when `J ≠ ∅`): the proof applies Theorem 4 to
   `P_N ∗ µ_N`, which needs `P_N ∗ µ_N` concentrated where the moduli hold; the moduli only
   control the `f_j` on `conv(𝒳)`, and without the condition the theorem is false
   (`𝒳 = {0}`, `P = δ₀`, `f₁(u, η, x) = u² + u·1_{x ≠ 0}`, `f₂ = 0`, `J = {1}`,
   `µ_N` uniform on `[−1/N, 1/N]`: the estimator is `u² + u`, `ϑ^{(N,J)}_µ = −1/4 ↛ 0 = ϑ`).
   It is required only for large `N`, since only the tail of the sequence matters.
   Taking `𝒳 = ℝ^m` always satisfies it.
4. The smoothed integrals `∫ f_j(u, η, x_i + z) dµ_N(z)` are not assumed to exist off `𝒰 × I_j`;
   where they do not, Lean's integral is `0` and the paper's estimator is undefined, so the
   statement covers every case in which the paper's estimator is defined.
5. The printed "Assumption 2" is Assumption 6; "for all `u ∈ U`" in the first bullet is read as
   `u ∈ 𝒰`. One null set serves all `u ∈ 𝒰`. -/
theorem smoothed_estimator_slln {n mX k : ℕ} (D : CompositeModel n mX k)
    (P : Measure (EuclideanSpace ℝ (Fin mX))) (𝒳 : Set (EuclideanSpace ℝ (Fin mX)))
    (U 𝒰 : Set (EuclideanSpace ℝ (Fin n)))
    (I : (j : ℕ) → Set (EuclideanSpace ℝ (Fin (D.m j))))
    (hstd : StandingAssumptions D P 𝒳 U 𝒰 I)
    (hPmom : Integrable (fun x => ‖x‖) P)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin mX)) (hindep : iIndepFun X Pr)
    (hlaw : ∀ i, HasLaw (X i) P Pr)
    (J : Finset ℕ) (hJ : J ⊆ Finset.Icc 1 (k + 1))
    (μ : ℕ → Measure (EuclideanSpace ℝ (Fin mX))) (hμ : SmoothingAssumption μ)
    (hsmooth𝒳 : J.Nonempty → ∀ᶠ N in atTop, ∀ᵐ x ∂P, ∀ᵐ z ∂(μ N),
      x + z ∈ closedConvexHull ℝ 𝒳)
    (w : (j : ℕ) → Fin (D.m (j - 1)) → ℝ → ℝ)
    (hw : ∀ j ∈ J, j ≤ k → ∀ i, IsModulus (w j i))
    (hmod : ∀ j ∈ J, j ≤ k → ∀ u ∈ 𝒰, ∀ η ∈ I j, ∀ i,
      ∀ x ∈ closedConvexHull ℝ 𝒳, ∀ x' ∈ closedConvexHull ℝ 𝒳,
        |D.f j u η x i - D.f j u η x' i| ≤ w j i ‖x - x'‖)
    (wLast : Fin (D.m k) → ℝ → ℝ)
    (hwLast : k + 1 ∈ J → ∀ i, IsModulus (wLast i))
    (hmodLast : k + 1 ∈ J → ∀ u ∈ 𝒰, ∀ i,
      ∀ x ∈ closedConvexHull ℝ 𝒳, ∀ x' ∈ closedConvexHull ℝ 𝒳,
        |D.fLast u x i - D.fLast u x' i| ≤ wLast i ‖x - x'‖)
    (g : EuclideanSpace ℝ (Fin mX) → ℝ) (hg : Integrable g P)
    (henv : ∀ j, 1 ≤ j → j ≤ k → j ∉ J → ∀ u ∈ 𝒰, ∀ η ∈ I j, ∀ x ∈ 𝒳, ‖D.f j u η x‖ ≤ g x)
    (henvLast : k + 1 ∉ J → ∀ u ∈ 𝒰, ∀ x ∈ 𝒳, ‖D.fLast u x‖ ≤ g x)
    (hA2 : ∀ᵐ ω ∂Pr, ∀ᶠ N in atTop,
      (solutionSet (mixedEstimator D J (μ N) N (fun i => X i ω)) U).Nonempty ∧
        solutionSet (mixedEstimator D J (μ N) N (fun i => X i ω)) U ⊆ 𝒰) :
    ∀ᵐ ω ∂Pr,
      (∀ u ∈ 𝒰, Tendsto (fun N => mixedEstimator D J (μ N) N (fun i => X i ω) u) atTop
          (𝓝 (riskFunctional D P u))) ∧
        Tendsto (fun N => optimalValue (mixedEstimator D J (μ N) N (fun i => X i ω)) U) atTop
          (𝓝 (optimalValue (riskFunctional D P) U)) ∧
        Tendsto (fun N => excess (solutionSet (mixedEstimator D J (μ N) N (fun i => X i ω)) U)
          (solutionSet (riskFunctional D P) U)) atTop (𝓝 0) ∧
        ∀ û, solutionSet (riskFunctional D P) U = {û} →
          Tendsto (fun N => Metric.hausdorffEDist
            (solutionSet (mixedEstimator D J (μ N) N (fun i => X i ω)) U)
            (solutionSet (riskFunctional D P) U)) atTop (𝓝 0) := by sorry

end CompositeSAA
