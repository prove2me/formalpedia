-- Prove2me | Theorems.Thm_DiffCtrlRobust_strong_solution_markov
-- name    : DiffCtrlRobust.strong_solution_markov
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:49:16.521185+00:00
-- url     : https://prove2.me/theorems/388f76f6-5ee5-4696-af48-cbc3c3dfd9fa
-- title:
--   §2, p.6 — under (A1)–(A3), (2.1) has a unique strong solution for every admissible control, and a unique strong, strong Feller solution for every $v\in\mathfrak U_{\mathsf{sm}}$
-- statement:
--   Let $W$ be a $d$-dimensional standard Wiener process on a probability space, let $\mathbb U$ be a compact metric space, and let $(b,\sigma)$ satisfy (A1)–(A3).
--
--   0. For every $x\in\mathbb R^d$ and every admissible control $U$ (a jointly measurable $\mathrm V$-valued process such that $W_t-W_s$ is independent of the completion of $\sigma(X_0,U_r,W_r:r\le s)$ for $s\le t$), the equation $\mathrm dX_t=b(X_t,U_t)\,\mathrm dt+\sigma(X_t)\,\mathrm dW_t$, $X_0=x$, has a strong solution, and any two strong solutions are indistinguishable.
--
--   For every stationary Markov control $v\in\mathfrak U_{\mathsf{sm}}$:
--
--   1. for every $x\in\mathbb R^d$ the equation
--
--   $$
--   \mathrm dX_t=b(X_t,v(X_t))\,\mathrm dt+\sigma(X_t)\,\mathrm dW_t,\qquad X_0=x,
--   $$
--
--   has a strong solution;
--   2. any two strong solutions from $x$ are indistinguishable;
--   3. the solutions are strong Feller: for $t>0$ and bounded Borel $f$, the map $x\mapsto\mathbb E\,f(X^x_t)$ is continuous.
--
--   Every cost of a stationary Markov control in this mission refers to this solution. The drift is only measurable in $x$, because $v$ is, so this is not the classical Lipschitz theory.
--
--   Differences from the source:
--
--   - encoding: complete probability space (Ω, 𝔉, ℙ) → any probability space, with the null sets joined to the filtrations explicitly; reason: the filtrations are the same up to null sets and no argument needs more; every complete space is included
--   - encoding: V-valued process U, 𝔘 implicit → jointly measurable U, admissible pairs (U, X) with X adapted to 𝔉; reason: makes 'V valued process' and 'strong solution' precise; the same controls
--   - encoding: sup over ζ in (A2) → a bound for every ζ; reason: equivalent for nonempty U
--   - encoding: U a compact metric space, min over U → U also nonempty; reason: a minimum over U presupposes it
--   - encoding: strong Feller (therefore strong Markov) process → the strong Feller property as continuity of x ↦ 𝔼 f(Xˣ_t); reason: 'strong Markov' is the paper's stated consequence of strong Feller and path continuity and is not used in §3
-- source:
--   Pradhan & Yüksel, arXiv:2205.05894v2, §2, p.6, citing [9, Theorem 2.2.4] and [9, Theorem 2.2.12]

import Definitions.Def_DiffCtrlRobust_A123
import Definitions.Def_DiffCtrlRobust_SolvesMarkov
import Definitions.Def_DiffCtrlRobust_IsAdmissibleSolution
import Definitions.Def_EthierKurtz_IsStandardBrownian

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

namespace DiffCtrlRobust

/-- Well-posedness of (2.1) (arXiv:2205.05894v2, §2, p.6, citing Arapostathis–Borkar–Ghosh,
Theorems 2.2.4 and 2.2.12): under (A1)–(A3), for any admissible control (2.1) has a unique strong
solution, and for every `v ∈ 𝔘sm`, (2.1) has a unique strong solution from every `x`, and it is a
strong Feller process.

**Formalization Note.** An admissible control from `x` is a jointly measurable `V`-valued process
`u` whose Brownian increments `W_t - W_s` are independent of `𝔉_s` (`admissiblePast`); its strong
solution is an `X` with `IsAdmissibleSolution`. Uniqueness is indistinguishability. The strong
Feller property is continuity of `x ↦ 𝔼 f(Xˣ_t)` for `t > 0` and bounded Borel `f`. -/
theorem strong_solution_markov {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} {U : Type*} [MetricSpace U] [CompactSpace U] [Nonempty U]
    [MeasurableSpace U] [BorelSpace U]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W)
    {C : ℝ → ℝ} {C₀ : ℝ} {b : SDEState d → U → SDEState d}
    {σ : SDEState d → SDEDiffusion d} (hA : A123 C C₀ b σ) (v : Usm d U) :
    (∀ (x : SDEState d) (u : ℝ≥0 → Ω → ProbabilityMeasure U),
      Measurable (fun p : ℝ≥0 × Ω => u p.1 p.2) →
      (∀ s t : ℝ≥0, s ≤ t → Indep (MeasurableSpace.comap (fun ω => W t ω - W s ω) inferInstance)
        (admissiblePast P W u (fun _ => x) s) P) →
      (∃ X, IsAdmissibleSolution P W b σ x u X) ∧
      ∀ X Y, IsAdmissibleSolution P W b σ x u X → IsAdmissibleSolution P W b σ x u Y →
        ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω) ∧
    (∀ x, ∃ X, SolvesMarkov P W b σ v x X) ∧
    (∀ x X Y, SolvesMarkov P W b σ v x X → SolvesMarkov P W b σ v x Y →
      ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω) ∧
    (∀ t : ℝ≥0, 0 < t → ∀ f : SDEState d → ℝ, Measurable f → (∃ K : ℝ, ∀ y, |f y| ≤ K) →
      ∀ Xs : SDEState d → ℝ≥0 → Ω → SDEState d, (∀ x, SolvesMarkov P W b σ v x (Xs x)) →
        Continuous (fun x => ∫ ω, f (Xs x t ω) ∂P)) := by sorry

end DiffCtrlRobust
