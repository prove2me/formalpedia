-- Prove2me | Theorems.Thm_FBMStrongSim_RecordBreak_theorem_3_5
-- name    : FBMStrongSim.RecordBreak.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:50.385771+00:00
-- url     : https://prove2.me/theorems/56b12b6c-60d4-4dfb-ac47-988f8aebc344
-- title:
--   Theorem 3.5, p. 11 — the dyadic discretizations B^H_n converge a.s. in C([0,1]) to a fBM (a continuous modification of B^H)
-- statement:
--   Let $B$ be a fractional Brownian motion on $[0,1]$ with Hurst index $H\in(0,1)$, with no assumption on its paths, and let $B_n$ be its dyadic discretization of level $n$ (the piecewise-linear interpolation of $B$ on $D_n$). Then there is a process $X$ such that
--
--   1. $X$ is a fractional Brownian motion on $[0,1]$ with Hurst index $H$;
--   2. almost surely, $X$ has continuous paths on $[0,1]$ and
--   $$\lim_{n\to\infty}\sup_{t\in[0,1]}|B_n(t)-X(t)|=0;$$
--   3. $X$ is a modification of $B$: $X(t)=B(t)$ almost surely for each $t\in[0,1]$.
--
--   This is the validity of the series expansion (2.2): the sample paths of $B_n$ converge to a fBM in $C([0,1])$ almost surely.
--
--   **Formalization Note** The paper fixes the continuous modification of fBM once (p. 5) and states the theorem as $\mathbb P(\lim_n\|B_n-B\|_\infty=0)=1$. With continuous paths assumed, that form would follow from uniform continuity alone; the statement here instead follows the proof (pp. 11–12): the limit of the dyadic discretizations exists without any path assumption and is a continuous fBM agreeing with $B$ at every fixed time almost surely.
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, p. 11, Theorem 3.5 (proof pp. 11–12)

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FBMStrongSim.RecordBreak

/-- Theorem 3.5, p. 11, in the form its proof gives: the dyadic discretizations `B^H_n` of a
fractional Brownian motion converge almost surely, uniformly on `[0,1]`, to a process `X` that
has continuous paths on `[0,1]`, is itself a fractional Brownian motion with Hurst index `H`, and
is a modification of `B` on `[0,1]`. No path regularity of `B` is assumed. -/
theorem theorem_3_5 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {H : ℝ} (hH0 : 0 < H) (hH1 : H < 1) {B : ℝ → Ω → ℝ} (hB : IsFBM H B P) :
    ∃ X : ℝ → Ω → ℝ, IsFBM H X P ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Icc 0 1) ∧
        TendstoUniformlyOn (fun (n : ℕ) (t : ℝ) => interp (fun s => B s ω) n t)
          (fun t => X t ω) Filter.atTop (Set.Icc 0 1)) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, X t =ᵐ[P] B t := by sorry

end FBMStrongSim.RecordBreak
