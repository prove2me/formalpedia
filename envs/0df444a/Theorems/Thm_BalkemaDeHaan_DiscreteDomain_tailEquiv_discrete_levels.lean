-- Prove2me | Theorems.Thm_BalkemaDeHaan_DiscreteDomain_tailEquiv_discrete_levels
-- name    : BalkemaDeHaan.DiscreteDomain.tailEquiv_discrete_levels
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:28.10226+00:00
-- url     : https://prove2.me/theorems/5e1a17fb-dfcf-4200-9d7e-3692248e4011
-- title:
--   Proof of Theorem 5, p. 800 — F ∈ D_r(Π_{p,c}) is tail equivalent to a discrete F₀ taking only the values F(b_n)
-- statement:
--   Let $p > 0$, $c \ge 0$ and $F = 1 - R \in D_r(\Pi_{p,c})$. Then there is a strictly increasing sequence $b_n \uparrow \infty$ with
--   $$\frac{R(b_{n+1})}{R(b_n)} \to e^{-p},$$
--   and a discrete distribution function $F_0 = 1 - R_0$ with jumps at an unbounded increasing sequence $t_0 < t_1 < \cdots$, such that $F_0$ only takes the values $F(b_n)$ (besides $0$),
--   $$F_0(s) = F(b_n) \quad \text{for } t_n \le s < t_{n+1}, \quad\text{i.e. } R_0(t_n) = R(b_n),$$
--   and $F$ is tail equivalent to $F_0$.
--
--   This is the first step of the "only if" half of Theorem 5: it produces the discrete law $F_0$ of the theorem.
--
--   **Formalization Note** In the proof, $b_n$ is built by iterating the shift of the normalization in the convention (2)–(3) of p. 794 (where $b(t)$ shifts $X$, not $X - t$): $b_{n+1} = b(b_n)$. The statement only asserts the existence of such a sequence, together with its tail-ratio property, which is what the rest of the proof uses. The page leaves the construction of $F_0$ implicit ("a distribution $F_0$ which only takes the values $F(b_n)$"); it is formalized with the level identity $R_0(t_n) = R(b_n)$ for every $n \ge 0$, which is how the next paragraph of the page uses $F_0$ ("$F_0(t) = F(b_n)$ for $t_n \le t < t_{n+1}$"). Indexing from $n = 0$ rather than the page's $n = 1$ is immaterial because $b$ is existential.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 800 (PDF 9), proof of Theorem 5, second and third paragraphs

import Mathlib
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_ResidualLife
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_PiPC
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_DiscreteLaw

open MeasureTheory Filter Topology

namespace BalkemaDeHaan.DiscreteDomain

/-- Proof of Theorem 5, p. 800 (PDF 9): if `F = 1 - R ∈ D_r(Π_{p,c})`, there is a sequence
`b_n ↑ ∞` with `R(b_{n+1})/R(b_n) → e^{-p}`, and `F` is BalkemaDeHaan.LimitTypes.tail equivalent to a discrete law `F₀`
with jumps `t₀ < t₁ < ⋯ → ∞` taking only the values `F(b_n)`: `F₀(s) = F(b_n)` for
`t_n ≤ s < t_{n+1}`, i.e. `R₀(t_n) = R(b_n)`. -/
theorem tailEquiv_discrete_levels (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : InDr μ (piPC p c)) :
    ∃ b : ℕ → ℝ, StrictMono b ∧ Tendsto b atTop atTop ∧
      Tendsto (fun n : ℕ => (μ (Set.Ioi (b (n + 1)))).toReal / (μ (Set.Ioi (b n))).toReal)
        atTop (𝓝 (Real.exp (-p))) ∧
      ∃ ν₀ : Measure ℝ, IsProbabilityMeasure ν₀ ∧ ∃ t : ℕ → ℝ,
        IsDiscreteWithJumps ν₀ t ∧ (∀ n, ν₀ (Set.Ioi (t n)) = μ (Set.Ioi (b n))) ∧
        TailEquiv μ ν₀ := by sorry

end BalkemaDeHaan.DiscreteDomain
