-- Prove2me | Theorems.Thm_BalkemaDeHaan_DiscreteDomain_levels_12b_12a
-- name    : BalkemaDeHaan.DiscreteDomain.levels_12b_12a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:49.068955+00:00
-- url     : https://prove2.me/theorems/785f52bd-c479-4efa-b252-774c28d70cef
-- title:
--   Proof of Theorem 5, pp. 800–801 — the discrete law F₀ satisfies (12b) and (12a)
-- statement:
--   Let $p > 0$, $c \ge 0$ and $F = 1 - R \in D_r(\Pi_{p,c})$. Let $(b_n)$ be a sequence with $R(b_{n+1})/R(b_n) \to e^{-p}$, and let $F_0 = 1 - R_0$ be a discrete distribution function with jumps at an unbounded increasing sequence $t_0 < t_1 < \cdots$, tail equivalent to $F$, with
--   $$R_0(t_n) = R(b_n) \quad \text{for all } n.$$
--   Then $F_0$ satisfies (12b) and its jumps satisfy (12a):
--   $$\frac{R_0(t_{n+1})}{R_0(t_n)} \to e^{-p}, \qquad \frac{t_{n+1}-t_n}{t_n - t_{n-1}} \to e^{pc}.$$
--
--   Combined with the previous milestone this is the "only if" half of Theorem 5.
--
--   **Formalization Note** The page obtains (12a) with limit $A$, the scale constant of the functional equation $S(x)S(0) = S(B + xA)$ for the tail $S$ of a translate of $\Pi_{p,c}$; this $A$ is the ratio of successive gaps between the jumps of $\Pi_{p,c}$, which is $e^{pc}$, and the statement says so. The level identity $R_0(t_n) = R(b_n)$ is a hypothesis, as on the page; it cannot be dropped: a law tail equivalent to $F$ may carry extra atoms of vanishing relative mass, at which (12a) and (12b) fail.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), pp. 800–801 (PDF 9–10), proof of Theorem 5, last paragraphs

import Mathlib
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_ResidualLife
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_PiPC
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_DiscreteLaw

open MeasureTheory Filter Topology

namespace BalkemaDeHaan.DiscreteDomain

/-- Proof of Theorem 5, pp. 800–801 (PDF 9–10): if `F ∈ D_r(Π_{p,c})` and `F₀` is a discrete law
with jumps `t₀ < t₁ < ⋯ → ∞`, BalkemaDeHaan.LimitTypes.tail equivalent to `F`, with `R₀(t_n) = R(b_n)` for a sequence
with `R(b_{n+1})/R(b_n) → e^{-p}`, then `F₀` satisfies (12b) and its jumps satisfy (12a). -/
theorem levels_12b_12a (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : InDr μ (piPC p c))
    (b : ℕ → ℝ)
    (hb : Tendsto (fun n : ℕ => (μ (Set.Ioi (b (n + 1)))).toReal / (μ (Set.Ioi (b n))).toReal)
      atTop (𝓝 (Real.exp (-p))))
    (ν₀ : Measure ℝ) [IsProbabilityMeasure ν₀] (t : ℕ → ℝ)
    (hν₀ : IsDiscreteWithJumps ν₀ t) (hlev : ∀ n, ν₀ (Set.Ioi (t n)) = μ (Set.Ioi (b n)))
    (heq : TailEquiv μ ν₀) :
    TailRatio ν₀ t p ∧ GapRatio t p c := by sorry

end BalkemaDeHaan.DiscreteDomain
