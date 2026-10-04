-- Prove2me | Theorems.Thm_BRWMinimum_Law_many_to_one
-- name    : BRWMinimum.Law.many_to_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T00:54:40.401987+00:00
-- url     : https://prove2.me/theorems/3db117e1-45d2-4b48-9258-e62fc73b62ca
-- title:
--   §2, eq. (2.1) — many-to-one lemma: 𝐄ₐ[Σ_{|x|=n} g(V(x₁),…,V(xₙ))] = 𝐄ₐ[e^{Sₙ−a} g(S₁,…,Sₙ)]
-- statement:
--   Let $(V(x),x\in\mathbb T)$ be a branching random walk with offspring law $\mathcal L$ in the boundary case (1.1), and let $\mu$ be the step law $\mu(B)=\mathbf E[\sum_{|x|=1}e^{-V(x)}\mathbf 1_B(V(x))]$. Then $\mu$ is a probability measure with finite mean $\int y\,\mu(dy)=0$, so the random walk $(S_n)$ with i.i.d. $\mu$-steps is centred. Moreover, for every $n\ge1$, every $a\in\mathbb R$ and every measurable $g:\mathbb R^n\to[0,\infty]$,
--   $$\mathbf E_a\Big[\sum_{|x|=n}g\big(V(x_1),\dots,V(x_n)\big)\Big]=\mathbf E_a\Big[e^{S_n-a}\,g(S_1,\dots,S_n)\Big],$$
--   where $\mathbf P_a$ is the law of the branching random walk started from $a$, $x_k$ is the ancestor of $x$ at generation $k$, and under $\mathbf P_a$ the walk starts at $S_0=a$.
--
--   This identity converts expectations of sums over the particles of a generation into expectations for a single random walk; every estimate of the paper starts from it.
--
--   **Formalization Note** The page asserts that *some* centred random walk satisfies (2.1); taking $n=1$ shows the step law must be $\mu$, so the statement is made for this explicit $\mu$. The walk started at $a$ is $a+S$ with $S$ started at $0$, hence the factor $e^{S_n-a}$ becomes $e^{\sum_{i<n}Y_i}$. Both sides are lower Lebesgue integrals in $[0,\infty]$. Only (1.1) is assumed, as on the page; the other standing assumptions are not needed.
-- source:
--   Aïdékon, Convergence in law of the minimum of a branching random walk, arXiv:1101.1810v6 (Ann. Probab. 41 (2013)), p. 4, §2, eq. (2.1)

import Mathlib
import Definitions.Def_BRWMinimum_Law_PointProcess
import Definitions.Def_BRWMinimum_Law_BRW
import Definitions.Def_BRWMinimum_Law_RandomWalk

open MeasureTheory ProbabilityTheory Filter Topology

namespace BRWMinimum.Law

/-- §2, eq. (2.1) (many-to-one lemma). -/
theorem many_to_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : List ℕ → Ω → PointConfig} {L : Measure PointConfig} [IsProbabilityMeasure L]
    (hξ : IsBRW P ξ L)
    (h11 : BoundaryCase L) :
    IsProbabilityMeasure (stepLaw L) ∧ Integrable (fun y : ℝ => y) (stepLaw L) ∧
      ∫ y, y ∂(stepLaw L) = 0 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ (a : ℝ) (g : (Fin n → ℝ) → ENNReal), Measurable g →
        ∫⁻ ω, ∑' u : {u : List ℕ // InTree ξ u ω ∧ u.length = n},
            g (fun k : Fin n => pos ξ a (u.1.take (k.1 + 1)) ω) ∂P =
          ∫⁻ s, ENNReal.ofReal (Real.exp (walk s n)) *
            g (fun k : Fin n => a + walk s (k.1 + 1)) ∂(walkLaw L) := by sorry

end BRWMinimum.Law
