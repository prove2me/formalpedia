-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_subseq_cylinder_limit
-- name    : FiniteEnergyPlane.exists_subseq_cylinder_limit
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-25T21:14:19.179565+00:00
-- url     : https://prove2.me/theorems/e0a71e02-bcd2-447d-927c-6113792e63c7
-- title:
--   Subsequential limits of a finite-energy plane along circles going to infinity
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, with associated almost complex structure $\tilde J$. Let $u:\mathbb C\to\mathbb R^{2n+2}\setminus\{0\}$ be a nonconstant finite-energy $\tilde J$-holomorphic plane, let $T=\int_{\mathbb C}u^*d\lambda$, and assume that $|z|\,|\nabla u(z)|$ is bounded on $\mathbb C$. Then for every sequence $R_k\to\infty$ there are a subsequence $(R_{k_j})$, a periodic Reeb orbit $P=(x,T)$ and $c\in\mathbb R$ such that
--
--   1. $t\mapsto\mathrm{proj}\,u\big(R_{k_j}e^{2\pi it}\big)$ converges to $t\mapsto x(Tt+c)$ in $C^\infty(\mathbb R,\mathbb R^{2n+2})$, and
--   2. for every $L\in\mathbb R$, $\;a\big(u(e^{2\pi L}R_{k_j})\big)-a\big(u(R_{k_j})\big)\to TL$ as $j\to\infty$.
--
--   **Formalization Note** $|\nabla u|$ is `gradNorm H u`, $a$ is `aCoord H`, $\mathrm{proj}$ is `proj H`, and $T$ is `(dlambdaEnergy H Set.univ u).toReal`. A Reeb orbit `P : ReebOrbit H` has period `P.T`, which need not be minimal. $C^\infty$ convergence is `TendstoCInfty`: uniform convergence on $\mathbb R$ of every derivative. In item 2 the points $e^{2\pi L}R_{k_j}$ and $R_{k_j}$ are real numbers viewed in $\mathbb C$.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, proof of Theorem 31, pp. 537–538

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Limits of a finite-energy plane along circles going to infinity (Hofer 1993, Thm. 31,
p. 537). Let `u` be a nonconstant finite-energy `J̃`-holomorphic plane with `dλ`-energy `T`, such
that `|z| · |∇u(z)|` (the `ℝ`-invariant norm `gradNorm`) is bounded on `ℂ`. For every sequence
`R_k → ∞` there are a subsequence `R_{k_j}`, a periodic Reeb orbit `P = (x, T)` and `c ∈ ℝ` such
that the loops `t ↦ proj(u(R_{k_j} e^{2π i t}))` converge in `C^∞` to `t ↦ x(T t + c)`, and for
every `L ∈ ℝ` the increments `a(u(e^{2πL} R_{k_j})) - a(u(R_{k_j}))` converge to `T L`. -/
theorem exists_subseq_cylinder_limit {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (hnc : ∃ z₁ z₂, u z₁ ≠ u z₂)
    (hG : ∃ C : ℝ, ∀ z : ℂ, ‖z‖ * gradNorm H u z ≤ C) (R : ℕ → ℝ)
    (hR : Tendsto R atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : ReebOrbit H,
      P.T = (dlambdaEnergy H Set.univ u).toReal ∧ ∃ c : ℝ,
        TendstoCInfty (fun j => loopInS H u (ccwLoop (R (φ j)))) (fun t => P.x (P.T * t + c)) ∧
        ∀ L : ℝ, Tendsto (fun j => aCoord H (u ((Real.exp (2 * π * L) * R (φ j) : ℝ) : ℂ)) -
          aCoord H (u ((R (φ j) : ℝ) : ℂ))) atTop (𝓝 (P.T * L)) := by
  sorry

end FiniteEnergyPlane
