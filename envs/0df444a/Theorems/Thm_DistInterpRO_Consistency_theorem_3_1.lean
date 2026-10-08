-- Prove2me | Theorems.Thm_DistInterpRO_Consistency_theorem_3_1
-- name    : DistInterpRO.Consistency.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:50:56.901918+00:00
-- url     : https://prove2.me/theorems/8fa0c6cb-a774-4343-ac34-d68f610f2f5e
-- title:
--   Theorem 3.1 — box-robust sample average optimization is consistent
-- statement:
--   Let $V$ be a set of decisions, $\mathcal F\subseteq V$ a nonempty feasible set, and $f:V\times\mathbb R^m\to\mathbb R$ a utility with $f(v,\cdot)$ Borel measurable for every $v$, satisfying
--
--   1. **Boundedness:** $|f(v,x)|\le C$ for all $v,x$;
--   2. **Equicontinuity:** $d(\epsilon)\to0$ as $\epsilon\downarrow0$, where $d(\epsilon)=\sup_{v,x,\|\delta\|_\infty\le\epsilon}|f(v,x)-f(v,x+\delta)|$.
--
--   Let $h^*$ be a probability density on $\mathbb R^m$ and $x_1,x_2,\dots$ i.i.d. samples from $h^*$ on a probability space. Let $\epsilon(n)>0$ satisfy
--   $$\epsilon(n)\downarrow0,\qquad n\,\epsilon(n)^m\uparrow\infty .$$
--   For each $n$ and each sample, let $v(n)$ be **any** maximiser over $\mathcal F$ of the box-robust objective
--   $$v\ \mapsto\ \frac1n\sum_{i=1}^n\ \inf_{\|\delta_i\|_\infty\le\epsilon(n)} f(v,x_i+\delta_i).$$
--   Then, with probability one,
--   $$\lim_{n\to\infty}\int_{\mathbb R^m}f(v(n),x)\,h^*(x)\,dx\ =\ \sup_{v\in\mathcal F}\int_{\mathbb R^m}f(v,x)\,h^*(x)\,dx;$$
--   that is, the robust optimization formulation is consistent.
--
--   The theorem says that robustifying a sampled stochastic program with $\ell_\infty$ boxes whose radius shrinks at the stated rate recovers the optimal expected utility, under boundedness and equicontinuity alone.
--
--   **Formalization Note** $\mathbb R^m$ is `Fin m → ℝ` with the sup norm. The samples $x_1,x_2,\dots$ are `X 0, X 1, …` (independent via `iIndepFun`, each with law `volume.withDensity h*`), and the $n$-th problem uses the first $n$. The maximisers form an arbitrary selection `v n ω` of the argmax — no measurability is assumed and the statement holds for every such selection; the paper's "arg max" presupposes that a maximiser exists, which is taken as a hypothesis. Implicit hypotheses made explicit: $\mathcal F\neq\emptyset$, $\epsilon(n)>0$ (the kernel divides by $\epsilon(n)$), measurability of each $f(v,\cdot)$, and that $h^*$ is a Lebesgue density (the paper integrates $h^*(x)\,dx$). "$\max_{v,x}|f|\le C$" is read as the uniform bound $|f|\le C$, the "max" in $d$ as a supremum, and "$d(\epsilon)\downarrow0$" as $d(\epsilon)\to0$ as $\epsilon\downarrow0$ ($d$ is automatically nondecreasing). The monotonicity in "$\epsilon(n)\downarrow0$" and "$n\epsilon(n)^m\uparrow\infty$" is kept as printed. The supremum on the right is a real supremum over the nonempty set $\mathcal F$ of values bounded by $C$. Hypotheses range over all $v\in V$; instantiating $V=\mathcal F$ gives the version with hypotheses on $\mathcal F$ only.
-- source:
--   Xu, Caramanis and Mannor, A Distributional Interpretation of Robust Optimization, Math. Oper. Res. 37(1) (2012), p. 98, Theorem 3.1

import Mathlib
import Definitions.Def_DistInterpRO_Consistency_Model

open MeasureTheory Filter Topology ProbabilityTheory

namespace DistInterpRO.Consistency

theorem theorem_3_1 {V : Type*} {m : ℕ} (F : Set V) (hF : F.Nonempty)
    (f : V → (Fin m → ℝ) → ℝ) (hfm : ∀ v, Measurable (f v))
    (C : ℝ) (hfC : ∀ v x, |f v x| ≤ C)
    (hd : Tendsto (modulus f) (𝓝[>] 0) (𝓝 0))
    (hstar : (Fin m → ℝ) → ℝ) (hstar_nonneg : ∀ x, 0 ≤ hstar x)
    (hstar_int : Integrable hstar) (hstar_one : ∫ x, hstar x = 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → Fin m → ℝ) (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = volume.withDensity (fun x => ENNReal.ofReal (hstar x)))
    (ε : ℕ → ℝ) (hε_pos : ∀ n, 0 < ε n)
    (hε_anti : Antitone ε) (hε_lim : Tendsto ε atTop (𝓝 0))
    (hnε_mono : Monotone (fun n : ℕ => (n : ℝ) * ε n ^ m))
    (hnε_lim : Tendsto (fun n : ℕ => (n : ℝ) * ε n ^ m) atTop atTop)
    (v : ℕ → Ω → V)
    (hv : ∀ n ω, v n ω ∈ F ∧ ∀ w ∈ F,
      roObjective f (ε n) (fun i : Fin n => X i ω) w ≤
        roObjective f (ε n) (fun i : Fin n => X i ω) (v n ω)) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ∫ x, f (v n ω) x * hstar x) atTop
      (𝓝 (⨆ w : F, ∫ x, f w x * hstar x)) := by sorry

end DistInterpRO.Consistency
