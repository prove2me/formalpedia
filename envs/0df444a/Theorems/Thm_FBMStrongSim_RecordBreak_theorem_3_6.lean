-- Prove2me | Theorems.Thm_FBMStrongSim_RecordBreak_theorem_3_6
-- name    : FBMStrongSim.RecordBreak.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:46.030973+00:00
-- url     : https://prove2.me/theorems/79cc9c52-ede6-400b-a188-ae48c27f7855
-- title:
--   Theorem 3.6, p. 12 — the last record level N has E[exp{tN}] < ∞, and for n > N, ‖B^H − B^H_n‖∞ ≤ ρ2^{−(H−δ)(n+1)}/(1 − 2^{−(H−δ)})
-- statement:
--   Let $B$ be a fractional Brownian motion on $[0,1]$ with Hurst index $H\in(0,1)$ whose paths are almost surely continuous on $[0,1]$. Fix $\delta\in(0,H)$ and $\rho>0$, let $B_n$ be the dyadic discretization of level $n$, and let
--   $$N=\sup\Big\{k\ge1:\max_{0\le j\le 2^{k-1}-1}|a^k_j-b^k_j|\ge\rho\,2^{-(H-\delta)k}\Big\}$$
--   be the level of the last record-breaker. Then:
--
--   1. for every $t>0$, $\mathbb E\big[\exp\{tN\}\big]<\infty$;
--   2. almost surely, for every $n>N$,
--   $$\|B-B_n\|_\infty=\sup_{s\in[0,1]}|B(s)-B_n(s)|\le\frac{\rho\cdot 2^{-(H-\delta)(n+1)}}{1-2^{-(H-\delta)}} .$$
--
--   The first part says that the last record level, which the simulation algorithm must find, has a light tail; the second says that once it is found, every finer discretization is within an explicit, deterministic distance of the true path. Together they are the basis of the paper's $\varepsilon$-strong simulation of fBM.
--
--   **Formalization Note** $N$ is valued in $\mathbb N\cup\{\infty\}$ and $\exp\{tN\}$ in $[0,\infty]$ with $\exp\{t\cdot\infty\}=\infty$, so part 1 also forces $N<\infty$ almost surely. Any $\rho>0$ is admitted (the paper's $\rho=2(\nu+\nu^*)$ of Theorem 3.1 ranges over $(0,\infty)$). Path continuity is assumed almost surely, which is the paper's convention that "fBM" means its continuous modification (p. 5). The sup norm is stated pointwise for every $s\in[0,1]$.
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, p. 12, Theorem 3.6 (proof p. 13)

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FBMStrongSim.RecordBreak

/-- Theorem 3.6, p. 12: for every `δ ∈ (0, H)`, `ρ > 0` and `t > 0`, the last record level `N`
has `E[exp{tN}] < ∞`; and almost surely, for every `n > N`,
`‖B^H − B^H_n‖∞ ≤ ρ · 2^{−(H−δ)(n+1)} / (1 − 2^{−(H−δ)})` on `[0,1]`. -/
theorem theorem_3_6 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {H delta rho : ℝ} (hH0 : 0 < H) (hH1 : H < 1) (hdelta0 : 0 < delta) (hdeltaH : delta < H)
    (hrho : 0 < rho) {B : ℝ → Ω → ℝ} (hB : IsFBM H B P)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => B t ω) (Set.Icc 0 1)) :
    (∀ t : ℝ, 0 < t → ∫⁻ ω, expMul t (lastRecord rho H delta (fun s => B s ω)) ∂P < ⊤) ∧
    (∀ᵐ ω ∂P, ∀ n : ℕ, lastRecord rho H delta (fun s => B s ω) < n →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, |B s ω - interp (fun s => B s ω) n s|
        ≤ rho * (2 : ℝ) ^ (-(H - delta) * ((n : ℝ) + 1)) / (1 - (2 : ℝ) ^ (-(H - delta)))) := by sorry

end FBMStrongSim.RecordBreak
