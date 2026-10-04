-- Prove2me | Theorems.Thm_BRWMinimum_Law_minimum_tail_asymptotics
-- name    : BRWMinimum.Law.minimum_tail_asymptotics
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:42:51.286179+00:00
-- url     : https://prove2.me/theorems/8a44f922-8717-4b5e-9ba0-67b2ee557f8c
-- title:
--   Proposition 4.1 — |(e^z/z) 𝐏(Mₙ < (3/2) ln n − z) − C₁c₀| ≤ ε uniformly for z ∈ [A, (3/2) ln n − A]
-- statement:
--   Assume the standing assumptions (1.1), non-lattice $\mathcal L$, (1.3), (1.4). Let $C_1$ be the constant of Proposition 1.2 and $c_0=\lim_{x\to\infty}R(x)/x$ the constant of (2.13). For every $\varepsilon>0$ there exist an integer $N\ge1$ and a real $A>0$ such that for every $n\ge N$ and every $z\in[A,\frac32\ln n-A]$,
--   $$\Big|\frac{e^z}{z}\,\mathbf P\Big(M_n<\frac32\ln n-z\Big)-C_1c_0\Big|\le\varepsilon,$$
--   where $M_n$ is the minimum at generation $n$ of the branching random walk started at $0$.
--
--   This is the tail of the (unkilled) minimum: it decays like $C_1c_0\,z\,e^{-z}$, uniformly in a growing window. It is a slightly stronger form of Proposition 1.3 and is the input of the proof of Theorem 1.1.
--
--   **Formalization Note** "$C_1$ as in Proposition 1.2" is a hypothesis that $C_1$ satisfies Proposition 1.2 (such $C_1$ exists and is unique), and "$c_0$ as in (2.13)" is a hypothesis that $R(x)/x\to c_0$ (such $c_0$ exists by (2.13)). Both are proved by other milestones; the constant $C_1c_0$ is therefore the paper's, not one re-chosen for the occasion. $z\ge A>0$, so $e^z/z$ is never a division by $0$.
-- source:
--   Aïdékon, Convergence in law of the minimum of a branching random walk, arXiv:1101.1810v6 (Ann. Probab. 41 (2013)), p. 28, Proposition 4.1

import Mathlib
import Definitions.Def_BRWMinimum_Law_PointProcess
import Definitions.Def_BRWMinimum_Law_BRW
import Definitions.Def_BRWMinimum_Law_RandomWalk

open MeasureTheory ProbabilityTheory Filter Topology

namespace BRWMinimum.Law

/-- Proposition 4.1: `|(e^z/z) P(M_n < (3/2) ln n − z) − C₁c₀| ≤ ε` uniformly on the window,
with `C₁` the constant of Proposition 1.2 and `c₀` the limit (2.13). -/
theorem minimum_tail_asymptotics {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : List ℕ → Ω → PointConfig} {L : Measure PointConfig} [IsProbabilityMeasure L]
    (hξ : IsBRW P ξ L)
    (h11 : BoundaryCase L) (hNL : NonLattice L) (h13 : SecondMoment L) (h14 : LogMoments L)
    (C₁ : ℝ) (hC₁ : IsKilledTailConst P ξ C₁)
    (c₀ : ℝ) (hc₀ : Tendsto (fun x : ℝ => (renewalFn L x).toReal / x) atTop (𝓝 c₀)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧ ∃ A : ℝ, 0 < A ∧
      ∀ n : ℕ, N ≤ n → ∀ z ∈ Set.Icc A ((3 / 2 : ℝ) * Real.log n - A),
        |Real.exp z / z * (P {ω | minPos ξ 0 n ω <
            (((3 / 2 : ℝ) * Real.log n - z : ℝ) : EReal)}).toReal - C₁ * c₀| ≤ ε := by sorry

end BRWMinimum.Law
