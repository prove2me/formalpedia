-- Prove2me | Theorems.Thm_DirectedOpinion_Typical_theorem_2
-- name    : DirectedOpinion.Typical.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:39.937858+00:00
-- url     : https://prove2.me/theorems/abcfd173-ed91-4c93-bf4c-da7382bf3bd8
-- title:
--   Theorem 2, pp. 8–9 — on graph sequences admitting a strong coupling, the typical stationary opinion converges in conditional law to the root opinion 𝓡* of the local limit
-- statement:
--   Consider the random directed graph sequence $G(V_n,E_n;\mathscr A_n)$ with the signals and initial opinions of the setting, and suppose that it admits a strong coupling (Definition 4) with a marked directed graph $\mathcal G(\boldsymbol{\mathcal X})$. Assume $d>0$ and that the conditional law $\nu(\cdot)$ of the external signals given the vertex marks satisfies
--   $$d_1(\nu(\mathbf x),\nu(\tilde{\mathbf x}))\le K\rho(\mathbf x,\tilde{\mathbf x})\qquad\text{for all }\mathbf x,\tilde{\mathbf x}\in\mathcal S$$
--   for some constant $K<\infty$; assume the same of the kernel $\nu_0$ of the initial opinions. Let $I_n$ be uniformly chosen in $V_n$. Then there are laws $L_k$ on $\mathbb R^{k+1}$, $k\ge0$, and $L^*$ on $\mathbb R$, none depending on $n$, such that, writing $(\mathcal R^{(0)},\dots,\mathcal R^{(k)})\sim L_k$ and $\mathcal R^*\sim L^*$:
--   1. for every $k\ge0$,
--   $$d_1\Bigl(\mathcal L\bigl((R^{(r)}_{I_n})_{0\le r\le k}\mid\mathscr A_n\bigr),\,L_k\Bigr)\xrightarrow{P}0\quad\text{and}\quad\frac1n\sum_{i=1}^nf(R_i^{(k)})\xrightarrow{P}E\bigl[f(\mathcal R^{(k)})\bigr]$$
--   for every continuous $f:[-1,1]\to\mathbb R$, where $d_1$ uses the sup distance on $\mathbb R^{k+1}$;
--   2. for the stationary vector $R=\sum_{r\ge0}\bar\Delta^rW^{(r)}$ of each graph,
--   $$d_1\bigl(\mathcal L(R_{I_n}\mid\mathscr A_n),\,L^*\bigr)\xrightarrow{P}0\quad\text{and}\quad\frac1n\sum_{i=1}^nf(R_i)\xrightarrow{P}E\bigl[f(\mathcal R^*)\bigr]$$
--   for every continuous $f:[-1,1]\to\mathbb R$;
--   3. $\mathcal R^{(k)}\Rightarrow\mathcal R^*$ at a geometric rate:
--   $$d_1\bigl(\mathrm{law}\,\mathcal R^{(k)},\,L^*\bigr)\le(1-d)^k\Bigl(\frac2d+2\Bigr)\qquad\text{for every }k\ge0 .$$
--
--   Items 1 and 2 are the paper's statements that $\max_{r\le k}E[|R^{(r)}_{I_n}-\mathcal R^{(r)}|\mid\mathscr A_n]\xrightarrow{P}0$ and $E[|R_{I_n}-\mathcal R^*|\mid\mathscr A_n]\xrightarrow{P}0$ for random variables whose law does not depend on $\mathscr A_n$. $\mathcal R^*$ is the "typical" stationary opinion of a large graph: the root opinion of the local limit. By (3), $\frac1n\sum_i\mathbb 1(R_i\in A)$ is the conditional law of $R_{I_n}$ given the graph, so item 2 says that the empirical distribution of stationary opinions does not depend, asymptotically, on the realization of the graph.
--
--   **Formalization Note**
--   1. **Law form.** "There exist $\mathcal R^{(r)}$, $\mathcal R^*$ whose law does not depend on $\mathscr A_n$ with $E[|\cdot|\mid\mathscr A_n]\xrightarrow{P}0$" is stated as convergence in probability of the $d_1$ distance between the regular conditional law given $\mathscr A_n$ and a fixed law. The two are equivalent: a coupling bounds $d_1$, and conversely a conditionally optimal coupling exists.
--   2. **Stationary vector.** "A vector $R$ having the stationary distribution" is the paper's own choice $R=\sum_r\bar\Delta^rW^{(r)}$ (p. 27), whose law is the stationary law by Theorem 1.
--   3. **Initial opinions (disclosed addition).** The page requires only that $R^{(0)}$ be conditionally independent of the signals. Item 1 at $r=0$ is false for an arbitrary $R^{(0)}$ (e.g. $R^{(0)}\equiv(-1)^n$), and the proof (p. 26) copies $R^{(0)}$ from the graph onto the limit. The statement therefore assumes $R_i^{(0)}=\varphi(\mathbf X_i,V_i)$ with $V_i$ i.i.d. uniform and $\mathbf x\mapsto\mathrm{law}\,\varphi(\mathbf x,V)$ $d_1$-Lipschitz with the same $K$. This covers the paper's simulations and constant initial vectors. Items 2 and 3 do not involve the initial opinions of the graph.
--   4. **Rate.** The page says only "at a geometric rate"; the constant $(1-d)^k(2/d+2)$ is the one its proof gives through Theorem 1 on $\mathcal G(\boldsymbol{\mathcal X})$ (pp. 23, 28), and $d_1$ is the metric used for weak convergence on $[-1,1]$.
--   5. $f$ is any function continuous on $[-1,1]$; all opinions lie in $[-1,1]$. The $m$-th graph of the sequence has $m+1$ vertices; the limit $n\to\infty$ is unaffected.
--   6. **Disjoint in-components (added).** The strong coupling of the setting requires the depth-$k$ in-components of the two uniform vertices to be disjoint on the coupling event, which the proof (p. 25) uses and Definition 4 does not state; without it the empirical-average claims are false (a graph whose vertices all listen to one hub, whose signals then shift every opinion by a common random amount). See the Setting.
-- source:
--   Fraiman, Lin and Olvera-Cravioto, Opinion dynamics on directed complex networks, arXiv:2209.00969v2, pp. 8–9, Theorem 2

import Mathlib
import Definitions.Def_DirectedOpinion_Typical_GraphSeq

namespace DirectedOpinion.Typical

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- Theorem 2, pp. 8–9, in law form. Under a strong coupling with a limit graph of law `μlim`,
with `d > 0`, a signal kernel `ν(x) = law ζ(x, U)` that is `d₁`-Lipschitz in the mark with
constant `K`, and initial opinions `R_i^(0) = φ(X_i, V_i)` whose kernel is `d₁`-Lipschitz with the
same `K`, there are laws `L_k` on `ℝ^{k+1}` (`k ≥ 0`) and `L*` on `ℝ`, not depending on `m`, with:
1. for every `k`: the `d₁` distance (sup cost) between the conditional law given `𝒜_m` of
   `(R_{I_m}^(0), …, R_{I_m}^(k))` and `L_k` tends to `0` in probability, and for every `f`
   continuous on `[−1, 1]`, `(1/n) Σ_i f(R_i^(k)) → ∫ f(y_k) dL_k(y)` in probability;
2. for the stationary vector `R = Σ_r Δ̄^r W^(r)`: the `d₁` distance between the conditional law
   given `𝒜_m` of `R_{I_m}` and `L*` tends to `0` in probability, and for every `f` continuous on
   `[−1, 1]`, `(1/n) Σ_i f(R_i) → ∫ f dL*` in probability;
3. the time-`k` marginal of `L_k` converges to `L*` at a geometric rate:
   `d₁(L_k ∘ y_k⁻¹, L*) ≤ (1 − d)^k (2/d + 2)`. -/
theorem theorem_2 {Ω A : Type*} [MeasurableSpace Ω] [MetricSpace A] [MeasurableSpace A]
    [BorelSpace A] [PolishSpace A] (P : Measure Ω) [IsProbabilityMeasure P] (S : GraphSeq Ω A)
    (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ) (c d K : ℝ)
    (μlim : Measure (LimGraph A)) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
    (hSC : StrongCoupling P S 𝓖 μlim) (hd : 0 < d) (hK : KernelLipschitz ζ K)
    (hK0 : KernelLipschitz φ K) :
    ∃ (L : (k : ℕ) → ProbabilityMeasure (Fin (k + 1) → ℝ)) (Lstar : ProbabilityMeasure ℝ),
      (∀ k : ℕ,
        (∀ η : ℝ, 0 < η →
          Tendsto (fun m => P {ω | ENNReal.ofReal η ≤
              W1vec (trajCondLaw P S ζ φ c d m k ω) (L k : Measure (Fin (k + 1) → ℝ))})
            atTop (𝓝 0)) ∧
        ∀ f : ℝ → ℝ, ContinuousOn f (Icc (-1 : ℝ) 1) →
          TendstoInMeasure P (fun m ω => empAvg f (S.R ζ φ c d m k ω)) atTop
            (fun _ => ∫ y, f (y (Fin.last k)) ∂(L k : Measure (Fin (k + 1) → ℝ)))) ∧
      ((∀ η : ℝ, 0 < η →
          Tendsto (fun m => P {ω | ENNReal.ofReal η ≤
              W1 (statCondLaw P S ζ c d m ω) (Lstar : Measure ℝ)})
            atTop (𝓝 0)) ∧
        ∀ f : ℝ → ℝ, ContinuousOn f (Icc (-1 : ℝ) 1) →
          TendstoInMeasure P (fun m ω => empAvg f (S.Rstat ζ c d m ω)) atTop
            (fun _ => ∫ y, f y ∂(Lstar : Measure ℝ))) ∧
      ∀ k : ℕ,
        W1 ((L k : Measure (Fin (k + 1) → ℝ)).map (fun y => y (Fin.last k))) (Lstar : Measure ℝ) ≤
          ENNReal.ofReal ((1 - d) ^ k * (2 / d + 2)) := by sorry

end DirectedOpinion.Typical
