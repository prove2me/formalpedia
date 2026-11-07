-- Prove2me | Theorems.Thm_CutwidthCircuitLB_appendix_A_open_vertex
-- name    : CutwidthCircuitLB.appendix_A_open_vertex
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:25:38.952411+00:00
-- url     : https://prove2.me/theorems/c624eebc-0311-43ec-add3-1c34ef29ee9f
-- title:
--   Appendix A — $\Pr[v \text{ open at } t] = \frac12\sum \Pr[t \text{ separates}] \le \frac1{2\pi}\sum \arccos\langle y_e, y_f\rangle$
-- statement:
--   Let $y_0, y_1, y_2 \in \mathbb R^d$ be unit vectors (the edge vectors at a vertex $v$), $\omega$ a standard Gaussian vector and $k_e = \langle y_e, \omega\rangle$ the scores. For every threshold $t$,
--   $$
--   \Pr[v \text{ is open at } t] = \frac12 \sum_{\{e,f\}} \Pr[t \text{ separates } k_e, k_f] \;\le\; \frac{1}{2\pi} \sum_{\{e,f\}} \arccos\langle y_e, y_f\rangle ,
--   $$
--   where the sums are over the three pairs $\{e, f\}$ of the three edges and $v$ is open at $t$ if $t$ lies strictly inside the range of $k_0, k_1, k_2$.
--
--   A threshold strictly inside the range of three numbers separates exactly two of the three pairs (almost surely no score equals $t$), and the inequality is Sheppard's formula with the worst threshold $0$.
--
--   **Formalization Note** Stated for any three unit vectors in any dimension.
--
--   Differences from the source:
--   - generalization: the three edge vectors y_e at a vertex v of the kernel → any three unit vectors y_0, y_1, y_2 ∈ ℝ^d; reason: the display uses only that the y_e are unit vectors; the edge vectors are an instance
--   - encoding: the scores k_e of the three edges at v, standard Gaussians with correlations ⟨y_e, y_f⟩ → ⟨y_i, ω⟩ for i = 0, 1, 2 under one standard Gaussian vector ω (Mathlib stdGaussian) of ℝ^d; reason: Appendix A defines the scores as k_e = ⟨y_e, ω⟩; the Lean is that definition
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Appendix A, p.21 (display)

import Mathlib
import Definitions.Def_CutwidthCircuitLB_Separates
import Definitions.Def_CutwidthCircuitLB_IsOpenAt
open MeasureTheory ProbabilityTheory

namespace CutwidthCircuitLB

/-- **Appendix A, probability that a vertex is open** (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Appendix A, p.21, display): let the three
edges at a vertex `v` have unit vectors `y₀, y₁, y₂` and scores `k_e = ⟨y_e, ω⟩` for a standard
Gaussian vector `ω`. For every threshold `t`,
`Pr[v is open at t] = ½ ∑_({e,f} ∋ v) Pr[t separates k_e, k_f] ≤ (1/(2π)) ∑_({e,f} ∋ v) arccos⟨y_e, y_f⟩`,
the sums being over the three pairs of edges at `v`.

**Formalization Note** Stated for any three unit vectors of any `ℝ^d` (the paper's are the edge
vectors at one vertex). -/
theorem appendix_A_open_vertex (d : ℕ) (y : Fin 3 → EuclideanSpace ℝ (Fin d))
    (hy : ∀ i, ‖y i‖ = 1) (t : ℝ) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).real
        {ω | IsOpenAt t (inner ℝ (y 0) ω) (inner ℝ (y 1) ω) (inner ℝ (y 2) ω)} =
      1 / 2 * ((stdGaussian (EuclideanSpace ℝ (Fin d))).real
          {ω | Separates t (inner ℝ (y 0) ω) (inner ℝ (y 1) ω)} +
        (stdGaussian (EuclideanSpace ℝ (Fin d))).real
          {ω | Separates t (inner ℝ (y 0) ω) (inner ℝ (y 2) ω)} +
        (stdGaussian (EuclideanSpace ℝ (Fin d))).real
          {ω | Separates t (inner ℝ (y 1) ω) (inner ℝ (y 2) ω)}) ∧
    (stdGaussian (EuclideanSpace ℝ (Fin d))).real
        {ω | IsOpenAt t (inner ℝ (y 0) ω) (inner ℝ (y 1) ω) (inner ℝ (y 2) ω)} ≤
      1 / (2 * Real.pi) * (Real.arccos (inner ℝ (y 0) (y 1)) +
        Real.arccos (inner ℝ (y 0) (y 2)) + Real.arccos (inner ℝ (y 1) (y 2))) := by sorry

end CutwidthCircuitLB
