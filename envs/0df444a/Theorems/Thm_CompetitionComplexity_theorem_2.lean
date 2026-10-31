-- Prove2me | Theorems.Thm_CompetitionComplexity_theorem_2
-- name    : CompetitionComplexity.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:14.49667+00:00
-- url     : https://prove2.me/theorems/b7bbe092-be33-4ff4-81bf-f9fe98a40450
-- title:
--   Theorem 2 — for $\varepsilon>0$, $m\ge\phi(\varepsilon)n$ buyers give $(1+\varepsilon)A_m(F)\ge M_n(F)$ for every $F$; asymptotically tight; $\phi(\varepsilon)=\Theta(\log\log 1/\varepsilon)$
-- statement:
--   This is the paper's main result on the **approximate competition complexity** of dynamic pricing.
--
--   Let $F$ range over distributions on $[0,\infty)$ with finite mean, let $A_m(F)$ be the value of the optimal dynamic pricing policy with $m$ i.i.d. buyers ($A_0=0$, $A_{k+1}=\mathbb E\max\{X,A_k\}$), let $M_n(F)$ be the expected maximum of $n$ i.i.d. draws, and let
--   $$
--   \phi(\varepsilon)=\int_0^1\frac{dy}{y(1-\log y)+\varepsilon}.
--   $$
--   The theorem has three parts.
--
--   1. **Sufficiency.** For every $\varepsilon>0$, every integer $n\ge1$, every integer $m\ge\phi(\varepsilon)n$ and every distribution $F$,
--   $$
--   (1+\varepsilon)A_m(F)\ge M_n(F).
--   $$
--   2. **Growth of the threshold.** $\phi(\varepsilon)=\Theta(\log\log 1/\varepsilon)$ as $\varepsilon\to0^+$.
--   3. **Tightness.** For every $\varepsilon>0$ and $\delta>0$ there is $n_0$ such that for every $n\ge n_0$ there is a distribution $G$ with
--   $$
--   (1+\varepsilon)A_m(G)<M_n(G)\qquad\text{for every integer } m<(\phi(\varepsilon)-\delta)n .
--   $$
--
--   So dynamic pricing with $\phi(\varepsilon)n$ buyers is within a factor $1+\varepsilon$ of the optimal auction with $n$ buyers, no smaller linear factor suffices, and the factor grows only doubly logarithmically as $\varepsilon\to0$. By contrast, Theorem 1 of the paper shows that no number of extra buyers suffices for $\varepsilon=0$.
--
--   **Formalization Note** $A_m$ is the published recursion `CorreaThreshold.Adaptive.dpW` (with $A_1=\mathbb E\max\{X,0\}=\mathbb EX$ since $X\ge0$). $M_n$ is valued in $[0,\infty]$, so both comparisons are made after mapping $(1+\varepsilon)A_m$ into $[0,\infty]$. The growth statement is the asymptotic $\Theta$ relation along $\varepsilon\to0^+$.
--
--   Differences from the source:
--   - reading: "for any δ > 0, there exists a distribution G such that for n sufficiently large and m < (ϕ(ε) − δ)n, we have (1 + ε)Am(G) < Mn(G)" → ∀ δ > 0, ∃ n₀, ∀ n ≥ n₀, ∃ G, ∀ m with m < (ϕ(ε) − δ)n, (1 + ε)Aₘ(G) < Mₙ(G); reason: the source says G is fixed before n, but also defines competition complexity for fixed n (p.2) and states the converse as "for large n this is tight" (p.3); its proof (Lemma 4, Lemma 5(c), Theorem 3, Lemma 3) builds G from n, and the reading keeps G uniform in m, the strongest form that proof gives. The order with one G for all large n fails for every G with bounded support, since Aₘ(G) → ω₁(G) ≥ Mₙ(G) by Proposition 1(iii); for unbounded G it is neither proved in the source nor refuted here, so this is a reading and not a correction
--   - encoding: Mₙ(F) a real number compared with (1 + ε)Aₘ(F) → Mₙ in [0, ∞] (ENNReal) compared with ENNReal.ofReal((1 + ε)Aₘ); reason: Mₙ(F) is finite and (1 + ε)Aₘ(F) ≥ 0 for every distribution, so the comparison is unchanged
--   - encoding: ϕ(ε)n = Θ(log log 1/ε)n → Asymptotics.IsTheta (𝓝[>] 0) ϕ (ε ↦ log(log(1/ε))); reason: the Θ relation of the source, as ε → 0⁺
-- source:
--   Brustle, Correa, Dütting, Verdugo, The Competition Complexity of Dynamic Pricing, accepted manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), doi:10.1287/moor.2022.0230, Theorem 2, p.6

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting
import Definitions.Def_CompetitionComplexity_Distribution
import Definitions.Def_CompetitionComplexity_Phi

open MeasureTheory Filter Topology
open CorreaThreshold.Adaptive (dpW)

namespace CompetitionComplexity

/-- **Theorem 2** (approximate competition complexity).
Brustle, Correa, Dütting, Verdugo, *The Competition Complexity of Dynamic Pricing*, accepted
manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), Theorem 2, p.6:
"Let ε > 0 and let n be a positive integer. Then, for every m ≥ ϕ(ε)n = Θ(log log 1/ε)n, and every
distribution F we have (1 + ε)Am(F) ≥ Mn(F). Conversely, for any δ > 0, there exists a distribution
G such that for n sufficiently large and m < (ϕ(ε) − δ)n, we have (1 + ε)Am(G) < Mn(G)."

Three conjuncts: (1) sufficiency for every `ε > 0`, `n ≥ 1`, `m ≥ ϕ(ε)n` and distribution `F`;
(2) `ϕ(ε) = Θ(log log 1/ε)` as `ε → 0⁺`; (3) the converse.

**Formalization Note.** `Aₘ(F)` is the recursion `A₀ = 0`, `Aₖ₊₁ = E max(X, Aₖ)` (published
`CorreaThreshold.Adaptive.dpW`; `A₁ = E max(X, 0) = E X` since `X ≥ 0`). `Mₙ` is `Mval`, valued in
`[0, ∞]`, so the comparisons are with `ENNReal.ofReal ((1 + ε) Aₘ)`. The converse is read with the distribution chosen after `n` (for every `δ > 0` there is `n₀` such
that for every `n ≥ n₀` some distribution `G` works for every `m < (ϕ(ε) − δ)n`). Competition
complexity is the smallest `m` for a fixed `n` (p.2), Main Result 2 says "for large n this is
tight" (p.3), and the paper's proof builds `G` from `n` through Theorem 3 and Lemma 3. With one `G`
for all large `n` the sentence fails for every `G` with bounded support, since
`Aₘ(G) → ω₁(G) ≥ Mₙ(G)` (Proposition 1(iii)), and the proof gives it for no `G`. -/
theorem theorem_2 :
    (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, phi ε * n ≤ m →
      ∀ μ : Measure ℝ, IsDist μ → Mval μ n ≤ ENNReal.ofReal ((1 + ε) * dpW μ m)) ∧
    Asymptotics.IsTheta (𝓝[>] (0 : ℝ)) phi (fun ε => Real.log (Real.log (1 / ε))) ∧
    (∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ G : Measure ℝ, IsDist G ∧ ∀ m : ℕ, (m : ℝ) < (phi ε - δ) * n →
        ENNReal.ofReal ((1 + ε) * dpW G m) < Mval G n) := by sorry

end CompetitionComplexity
