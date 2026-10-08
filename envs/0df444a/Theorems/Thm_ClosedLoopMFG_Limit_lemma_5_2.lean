-- Prove2me | Theorems.Thm_ClosedLoopMFG_Limit_lemma_5_2
-- name    : ClosedLoopMFG.Limit.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:30:35.87999+00:00
-- url     : https://prove2.me/theorems/b36e3f1a-1ce9-47f0-899f-74951073b0ab
-- title:
--   Lemma 5.2 — projecting the drift of $h(Y)$ onto the natural filtration of $Y$
-- statement:
--   Let $(Y_t)_{t\in[0,T]}$ be a continuous stochastic process with values in a Polish space $E$, defined on a probability space $(\Omega,\mathcal F,\mathbb P)$, and let $h:E\to\mathbb R$ be continuous. Let $(a_t)_{t\in[0,T]}$ be a bounded measurable real-valued process such that, almost surely,
--   $$h(Y_t)=h(Y_0)+\int_0^t a_s\,ds\quad\text{for a.e. }t\in[0,T].$$
--   Let $\hat a:[0,T]\times C([0,T];E)\to\mathbb R$ be progressively measurable with
--   $$\hat a(t,Y)=\mathbb E\big[a_t\mid\mathcal F^Y_t\big]\ \text{a.s.},\quad\text{for a.e. }t\in[0,T],\qquad\mathcal F^Y_t=\sigma(Y_s:s\le t).$$
--   Then, almost surely,
--   $$h(Y_t)=h(Y_0)+\int_0^t\hat a(s,Y)\,ds\quad\text{for all }t\in[0,T].$$
--
--   This projection lemma replaces a non-adapted drift by its optional projection onto the filtration of the observed process; it is used to identify the limiting dynamics.
--
--   **Formalization Note** "Progressively measurable" is Borel measurability of $(t,y)\mapsto\hat a(t,y)$ together with $\hat a(t,y)=\hat a(t,y')$ whenever $y_s=y'_s$ for $s\le t$, as in footnote 3. "Measurable process" is joint measurability of $(t,\omega)\mapsto a_t(\omega)$. The printed hypothesis "it holds almost surely that … a.s., for a.e. $t$" is read as: almost surely, for a.e. $t$ (equivalent, by Fubini, to the other order). The path space $C([0,T];E)$ carries a Borel $\sigma$-field, supplied as a hypothesis instance.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, p. 25, Lemma 5.2

import Mathlib
import Definitions.Def_ClosedLoopMFG_Limit_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ClosedLoopMFG.Limit

/-- **Lemma 5.2** (p. 25). Let `Y` be a continuous process with values in a Polish space `X`,
`h : X → ℝ` continuous, `a` a bounded measurable real process with
`h(Y_t) = h(Y_0) + ∫_0^t a_s ds` a.s. for a.e. `t`, and `â` a progressively measurable function
on `[0, T] × C([0, T]; X)` with `â(t, Y) = E[a_t | 𝓕^Y_t]` a.s. for a.e. `t`. Then a.s.,
`h(Y_t) = h(Y_0) + ∫_0^t â(s, Y) ds` for all `t ∈ [0, T]`. -/
theorem lemma_5_2 {T : ℝ≥0} {X : Type} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] [MeasurableSpace C(Set.Icc (0 : ℝ) T, X)]
    [BorelSpace C(Set.Icc (0 : ℝ) T, X)]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → C(Set.Icc (0 : ℝ) T, X)) (hY : ∀ t, Measurable fun ω => Y ω t)
    (h : X → ℝ) (hh : Continuous h)
    (a : ℝ → Ω → ℝ) (ha : Measurable (Function.uncurry a)) (hab : ∃ C : ℝ, ∀ t ω, |a t ω| ≤ C)
    (heq : ∀ᵐ ω ∂P, ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      h (ev (Y ω) t) = h (ev (Y ω) 0) + ∫ s in (0 : ℝ)..t, a s ω)
    (ahat : ℝ → C(Set.Icc (0 : ℝ) T, X) → ℝ) (hahat : Measurable (Function.uncurry ahat))
    (hahat_prog : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ y y' : C(Set.Icc (0 : ℝ) T, X),
      (∀ s : Set.Icc (0 : ℝ) T, (s : ℝ) ≤ t → y s = y' s) → ahat t y = ahat t y')
    (hcond : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (fun ω => ahat t (Y ω)) =ᵐ[P]
        P[a t | ⨆ (s : Set.Icc (0 : ℝ) T) (_ : (s : ℝ) ≤ t),
          MeasurableSpace.comap (fun ω => Y ω s) inferInstance]) :
    ∀ᵐ ω ∂P, ∀ t : Set.Icc (0 : ℝ) T,
      h (Y ω t) = h (ev (Y ω) 0) + ∫ s in (0 : ℝ)..t, ahat s (Y ω) := by sorry

end ClosedLoopMFG.Limit
