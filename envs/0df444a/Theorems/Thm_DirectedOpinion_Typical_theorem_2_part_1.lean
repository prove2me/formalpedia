-- Prove2me | Theorems.Thm_DirectedOpinion_Typical_theorem_2_part_1
-- name    : DirectedOpinion.Typical.theorem_2_part_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:48.812815+00:00
-- url     : https://prove2.me/theorems/8e4c6da7-77be-41d8-9978-414a31b52145
-- title:
--   Theorem 2(1), p. 8 — the typical trajectory (R_{I_n}^(0),…,R_{I_n}^(k)) converges in conditional law to a fixed law, and (1/n)Σ_i f(R_i^(k)) →P E f(𝓡^(k))
-- statement:
--   Consider the random directed graph sequence $G(V_n,E_n;\mathscr A_n)$ with the signals and initial opinions of the setting, and suppose that it admits a strong coupling (Definition 4) with a marked directed graph $\mathcal G(\boldsymbol{\mathcal X})$. Assume $d>0$, that the signal kernel satisfies
--   $$d_1(\nu(\mathbf x),\nu(\tilde{\mathbf x}))\le K\rho(\mathbf x,\tilde{\mathbf x})\qquad\text{for all }\mathbf x,\tilde{\mathbf x}\in\mathcal S$$
--   for some constant $K<\infty$, and that the kernel $\nu_0(\mathbf x)$ of the initial opinions satisfies the same condition. Let $I_n$ be uniformly chosen in $V_n$ and fix $k\ge0$. Then there is a law $L_k$ on $\mathbb R^{k+1}$, not depending on $n$, such that
--   1. the conditional law of the trajectory $(R^{(0)}_{I_n},\dots,R^{(k)}_{I_n})$ given $\mathscr A_n$ converges to $L_k$ in probability, in the Wasserstein distance $d_1$ for the sup distance on $\mathbb R^{k+1}$:
--   $$d_1\Bigl(\mathcal L\bigl((R^{(r)}_{I_n})_{0\le r\le k}\mid\mathscr A_n\bigr),\,L_k\Bigr)\xrightarrow{P}0;$$
--   2. for every continuous $f:[-1,1]\to\mathbb R$, with $(\mathcal R^{(0)},\dots,\mathcal R^{(k)})\sim L_k$,
--   $$\frac1n\sum_{i=1}^nf(R_i^{(k)})\xrightarrow{P}E\bigl[f(\mathcal R^{(k)})\bigr],\qquad n\to\infty .$$
--
--   Item 1 is the paper's statement that a sequence $\{\mathcal R^{(r)}:0\le r\le k\}$ whose law does not depend on $\mathscr A_n$ satisfies $\max_{0\le r\le k}E[|R^{(r)}_{I_n}-\mathcal R^{(r)}|\mid\mathscr A_n]\xrightarrow{P}0$; $\mathcal R^{(r)}$ is the opinion at time $r$ of the root of the local limit.
--
--   **Formalization Note**
--   1. **Law form.** The existence of such $\mathcal R^{(r)}$, independent of $\mathscr A_n$ with a fixed law, is equivalent to the convergence in item 1: a coupling bounds $d_1$, and conversely a conditionally optimal coupling exists. The law form avoids constructing couplings on the given space.
--   2. **Initial opinions (disclosed addition).** The page requires only that $R^{(0)}$ be conditionally independent of the signals given the graph. At $r=0$ the statement is false for an arbitrary $R^{(0)}$ (e.g. $R^{(0)}\equiv(-1)^n$), and the proof (p. 26) copies $R^{(0)}$ from the graph onto the limit. The statement therefore assumes $R_i^{(0)}=\varphi(\mathbf X_i,V_i)$ with $V_i$ i.i.d. uniform and $\mathbf x\mapsto\mathrm{law}\,\varphi(\mathbf x,V)$ $d_1$-Lipschitz with the same $K$. This covers the paper's simulations (i.i.d. uniform on $\{-1,1\}$) and constant initial vectors.
--   3. $f$ is any function continuous on $[-1,1]$; all opinions lie in $[-1,1]$, so its values elsewhere do not matter.
--   4. The $m$-th graph of the sequence has $m+1$ vertices.
--   5. **Disjoint in-components (added).** The strong coupling of the setting requires the depth-$k$ in-components of the two uniform vertices to be disjoint on the coupling event, which the proof (p. 25) uses and Definition 4 does not state; without it the empirical-average claim is false (a graph whose vertices all listen to one hub). See the Setting.
-- source:
--   Fraiman, Lin and Olvera-Cravioto, Opinion dynamics on directed complex networks, arXiv:2209.00969v2, p. 8, Theorem 2, item 1

import Mathlib
import Definitions.Def_DirectedOpinion_Typical_GraphSeq

namespace DirectedOpinion.Typical

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- Theorem 2, part 1, p. 8, in law form. Under a strong coupling with a limit graph of law
`μlim`, with `d > 0`, a signal kernel `ν(x) = law ζ(x, U)` that is `d₁`-Lipschitz in the mark with
constant `K`, and initial opinions `R_i^(0) = φ(X_i, V_i)` whose kernel is `d₁`-Lipschitz with the
same `K`: for every `k ≥ 0` there is a law `L_k` on `ℝ^{k+1}` (not depending on `m`) such that
1. the `d₁` distance (sup cost) between the conditional law given `𝒜_m` of the trajectory
   `(R_{I_m}^(0), …, R_{I_m}^(k))` and `L_k` tends to `0` in probability, and
2. for every `f` continuous on `[−1, 1]`, `(1/n) Σ_i f(R_i^(k)) → ∫ f(y_k) dL_k(y)` in probability. -/
theorem theorem_2_part_1 {Ω A : Type*} [MeasurableSpace Ω] [MetricSpace A] [MeasurableSpace A]
    [BorelSpace A] [PolishSpace A] (P : Measure Ω) [IsProbabilityMeasure P] (S : GraphSeq Ω A)
    (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ) (c d K : ℝ)
    (μlim : Measure (LimGraph A)) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
    (hSC : StrongCoupling P S 𝓖 μlim) (hd : 0 < d) (hK : KernelLipschitz ζ K)
    (hK0 : KernelLipschitz φ K) (k : ℕ) :
    ∃ L : ProbabilityMeasure (Fin (k + 1) → ℝ),
      (∀ η : ℝ, 0 < η →
        Tendsto (fun m => P {ω | ENNReal.ofReal η ≤
            W1vec (trajCondLaw P S ζ φ c d m k ω) (L : Measure (Fin (k + 1) → ℝ))})
          atTop (𝓝 0)) ∧
      ∀ f : ℝ → ℝ, ContinuousOn f (Icc (-1 : ℝ) 1) →
        TendstoInMeasure P (fun m ω => empAvg f (S.R ζ φ c d m k ω)) atTop
          (fun _ => ∫ y, f (y (Fin.last k)) ∂(L : Measure (Fin (k + 1) → ℝ))) := by sorry

end DirectedOpinion.Typical
