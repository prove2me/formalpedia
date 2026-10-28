-- Prove2me | Theorems.Thm_ChanceStateCtrl_AlmostSure_theorem_3_9_existence
-- name    : ChanceStateCtrl.AlmostSure.theorem_3_9_existence
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-24T21:41:12.655068+00:00
-- url     : https://prove2.me/theorems/d349a76c-dbc8-497d-b8aa-4174baef3fd2
-- title:
--   Theorem 3.9 (Ioffe–Levin), existence part — $v^* = v^a + v^\circ$ with $\|v^*\| = \|v^a\| + \|v^\circ\|$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $X$ a separable real Banach space. Every continuous linear functional $v^*\in(L^\infty_{\mathbb P}(\Omega,X))^*$ can be written as
--   $$v^* = v^a + v^\circ,\qquad \|v^*\| = \|v^a\| + \|v^\circ\|,$$
--   where
--
--   - $v^a$ is **absolutely continuous**: there is $x^*:\Omega\to X^*$ in $\Lambda_1(X^*)$ (i.e. $\omega\mapsto\langle x^*(\omega),x\rangle$ is measurable for each $x\in X$ and $\int_\Omega\|x^*(\omega)\|\,d\mathbb P<\infty$) with $\langle v^a,x\rangle=\int_\Omega\langle x^*(\omega),x(\omega)\rangle\,d\mathbb P(\omega)$ for all $x\in L^\infty_{\mathbb P}(\Omega,X)$;
--   - $v^\circ$ is **singular** relative to $\mathbb P$: there is a decreasing sequence of measurable sets $F_n$ with $\mathbb P(F_n)\to0$ such that $\langle v^\circ,x\rangle=0$ for every $x$ vanishing a.s. on some $F_n$.
--
--   This is the existence half of Theorem 3.9 (Ioffe–Levin) as stated in Geiersbach–Henrion; the uniqueness half has been proved separately (it follows from the fact that a functional which is both absolutely continuous and singular vanishes).
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 21, Theorem 3.9 (existence part), citing Ioffe & Levin [24, Appendix 1, Theorem 3] and [30]; definitions (55), Λ₁(X*) on p. 21

import Mathlib
import Definitions.Def_ChanceStateCtrl_AlmostSure_Setting

open MeasureTheory

namespace ChanceStateCtrl.AlmostSure

/-- Theorem 3.9 (Ioffe and Levin), p. 21, existence part: every `v* ∈ (L∞_P(Ω, X))*`, `X` a
separable Banach space, splits as `v* = vᵃ + v°` with `vᵃ` absolutely continuous (represented by
some `x* ∈ Λ₁(X*)`), `v°` singular relative to `P`, and `‖v*‖ = ‖vᵃ‖ + ‖v°‖`. -/
theorem theorem_3_9_existence {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] (v : StrongDual ℝ (Lp X ⊤ P)) :
    ∃ va vs : StrongDual ℝ (Lp X ⊤ P), IsAbsCont P va ∧ IsSingular P vs ∧ v = va + vs ∧
        ‖v‖ = ‖va‖ + ‖vs‖ := by sorry

end ChanceStateCtrl.AlmostSure
