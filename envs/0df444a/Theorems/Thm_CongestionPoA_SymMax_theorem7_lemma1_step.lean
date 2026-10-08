-- Prove2me | Theorems.Thm_CongestionPoA_SymMax_theorem7_lemma1_step
-- name    : CongestionPoA.SymMax.theorem7_lemma1_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T09:11:40.021988+00:00
-- url     : https://prove2.me/theorems/2680dea1-729e-4c7e-b503-305b9d0df8c3
-- title:
--   Theorem 7, proof — by Lemma 1, $\sum_e n_e(P)f_e(n_e(A)+1)\le\frac13\mathrm{SUM}(A)+\frac53\mathrm{SUM}(P)$
-- statement:
--   Let $G$ be a congestion game with linear latencies $f_e(k)=a_ek+b_e$, $a_e,b_e\ge 0$, and let $A,P$ be any two strategy profiles. Then
--   $$\sum_{e\in E} n_e(P)\,f_e\big(n_e(A)+1\big)\;\le\;\tfrac13\,\mathrm{SUM}(A)+\tfrac53\,\mathrm{SUM}(P).$$
--
--   For the identity latencies of the printed proof, $\mathrm{SUM}(X)=\sum_e n_e(X)^2$ and this is the step "Using Lemma 1, the last expression is at most $\frac13\sum_e n_e^2(A)+\frac53\sum_e n_e^2(P)$" of the proof of Theorem 7.
--
--   **Formalization Note** For affine latencies the sums of squares are replaced by the social costs $\mathrm{SUM}(X)=\sum_e n_e(X)f_e(n_e(X))$. No equilibrium, feasibility or symmetry hypothesis is needed.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 5, Theorem 7, proof (third step, using Lemma 1 of PDF p. 3)

import Mathlib
import Definitions.Def_CongestionPoA_SymMax_Model

namespace CongestionPoA.SymMax

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 5, Theorem 7, proof (third step, "Using Lemma 1"): for linear latencies and any two profiles
`A, P`,
`Σ_{e∈E} n_e(P) f_e(n_e(A) + 1) ≤ (1/3)·SUM(A) + (5/3)·SUM(P)`.

**Formalization Note.** For the identity latencies of the printed proof `SUM(X) = Σ_e n_e(X)²` and this
is the page's "at most `(1/3)Σ_e n_e²(A) + (5/3)Σ_e n_e²(P)`". For affine latencies
`f_e(k) = a_e k + b_e`, `a_e, b_e ≥ 0`, the sums of squares are replaced by the social costs
`SUM(X) = Σ_e n_e(X) f_e(n_e(X))`, which is the form the rest of the proof uses. No equilibrium or
feasibility hypothesis is needed. -/
theorem theorem7_lemma1_step {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (G : CongestionGame ι E) (A P : ι → Finset E) (hlin : IsLinear G) :
    ∑ e, (load P e : ℝ) * G.latency e (load A e + 1) ≤
      1 / 3 * sumCost G A + 5 / 3 * sumCost G P := by sorry

end CongestionPoA.SymMax
