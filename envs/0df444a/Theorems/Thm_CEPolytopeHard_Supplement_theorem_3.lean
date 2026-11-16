-- Prove2me | Theorems.Thm_CEPolytopeHard_Supplement_theorem_3
-- name    : CEPolytopeHard.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:14:45.192399+00:00
-- url     : https://prove2.me/theorems/7352e270-ea04-4361-b326-14de69b96c82
-- title:
--   Theorem 3 — every randomized algorithm for a $d^{-c}$-correlated equilibrium with at most $d^C$ profiles needs $2^{\Omega(d/\log d)}$ utility queries
-- statement:
--   Consider two-player concave games on $X_1=X_2=[0,1]^d$ whose utilities $u_i:[0,1]^d\times[0,1]^d\to[0,1]$ are quadratic concave in the player's own strategy (as in Theorem 2) and have own-strategy gradients of Euclidean norm at most $1$. A **utility query** names a player $i$ and a profile $x\in[0,1]^d\times[0,1]^d$ and returns $u_i(x)$ and $\nabla_{x_i}u_i(x)$. A randomized algorithm draws a random seed and then runs a deterministic adaptive query algorithm, finally outputting a finite-support distribution on profiles.
--
--   **Theorem 3.** For every fixed $C\ge1$ there is a constant $c>0$ such that any randomized algorithm that, on every such game, computes with probability at least $2/3$ a $d^{-c}$-correlated equilibrium supported on at most $d^C$ profiles requires
--   $$2^{\Omega(d/\log d)}$$
--   utility queries in the worst case.
--
--   Precisely: there are $c>0$, $\kappa>0$ and $d_0$ such that for every $d\ge d_0$ and every randomized algorithm making at most $Q<2^{\kappa d/\ln d}$ queries, there is a game in the class on which the algorithm outputs such an equilibrium with probability less than $2/3$.
--
--   The bound is unconditional: it holds in the black-box model, where computation between queries is free.
--
--   **Formalization Note** The class is `QuadGame.Valid ∧ QuadGame.GradBounded`, algorithms are `QueryAlg`, and success is `SolvesCE`. Seeds form an arbitrary probability space; a non-measurable success event does not count as success with probability at least $2/3$.
--
--   Differences from the source:
--   - reading: "requires 2^{Ω(d/ log d)} utility queries in the worst case" → ∀ C ≥ 1, ∃ c > 0, ∃ κ > 0, ∃ d₀, ∀ d ≥ d₀, every budget Q < 2^{κd/ln d} fails on some game; reason: the standard meaning of an Ω lower bound; κ and d₀ may depend on C; the log base is absorbed in κ
--   - encoding: a randomized algorithm that, with probability at least 2/3, computes a solution → a probability space (Ω, P) of seeds and a deterministic adaptive algorithm A ω per seed, each run making exactly Q queries; failure on G is ¬(the seed set of success is measurable ∧ its probability ≥ 2/3); reason: worst-case query count; an arbitrary seed space covers every randomized algorithm; a non-measurable success event has no probability
--   - encoding: utility queries (Section 2.1: evaluation oracle and subgradient oracle of a concave function) → a query (i, p) with p ∈ [0,1]^d × [0,1]^d returns (u_i(p), ∇_{p_i} u_i(p)); a query outside the strategy space returns (0, 0); outputs are arbitrary real finite-support distributions; reason: the oracles are defined on X; computation between queries is free in the black-box model
--   - reading: "two-player concave games on [0,1]^d, where each utility is quadratic in the player’s own strategy" → QuadGame.Valid (opponent-only term allowed, A_i symmetric PSD, values in [0,1], continuous) and GradBounded (‖∇_{own}u_i‖₂ ≤ 1, unnormalized); reason: as in Theorem 2; the gradient bound is the promise of Section 2.1 that every negative result must respect
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Theorem 3, p.5 (proof sketch p.5: the reduction of Theorem 2 from the randomized query lower bound for Lipschitz fixed points [51, 72])

import Mathlib
import Definitions.Def_CEPolytopeHard_Supplement_QuadGame
import Definitions.Def_CEPolytopeHard_Supplement_QueryAlg

set_option autoImplicit false

namespace CEPolytopeHard.Supplement

open MeasureTheory

/-- **Theorem 3** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of
Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2,
2026, sha256 6aec500a…7820, Theorem 3, p.5): "For every fixed C ≥ 1, there is a constant c > 0
such that any randomized algorithm that, with probability at least 2/3, computes a
d^{−c}-correlated equilibrium supported on at most d^C profiles requires 2^{Ω(d/ log d)} utility
queries in the worst case. This holds even in two-player concave games on [0, 1]^d, where each
utility is quadratic in the player’s own strategy."

For every `C ≥ 1` there are `c > 0`, `κ > 0` and `d₀` such that for every `d ≥ d₀` and every
query budget `Q < 2^{κd/ln d}`, every randomized `Q`-query algorithm (a probability space of seeds
`(Ω, P)` and a deterministic algorithm `A ω` for each seed) fails on some valid quadratic concave
game `G` with bounded gradients: the set of seeds on which `A ω` outputs a solution after `Q`
queries is not a measurable set of probability at least `2/3`.

**Formalization Note** `Ω(d/log d)` is read as `κ d / ln d` for some `κ > 0` and all `d ≥ d₀`;
the budget `Q` bounds the number of queries of every run (worst case). A query returns the value
and the own-strategy gradient (Section 2.1). The game class carries the black-box promise
`‖∇_{own} u_i‖₂ ≤ 1` (unnormalized). Seeds form an arbitrary probability space; a seed set that is
not measurable is not a success "with probability at least 2/3". -/
theorem theorem_3 :
    ∀ C : ℝ, 1 ≤ C → ∃ c : ℝ, 0 < c ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ Q : ℕ, (Q : ℝ) < (2 : ℝ) ^ (κ * d / Real.log d) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (A : Ω → QueryAlg d),
      ∃ G : QuadGame d, G.Valid ∧ G.GradBounded ∧
        ¬ (MeasurableSet {ω | SolvesCE d C c G ((A ω).run G Q)} ∧
          (2 / 3 : ENNReal) ≤ P {ω | SolvesCE d C c G ((A ω).run G Q)}) := by sorry

end CEPolytopeHard.Supplement
