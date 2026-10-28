-- Prove2me | Theorems.Thm_ClosestString_PTAS_lemma_6_rounding
-- name    : ClosestString.PTAS.lemma_6_rounding
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T16:17:36.952565+00:00
-- url     : https://prove2.me/theorems/45081b16-2cab-435b-94d4-97b531adee3e
-- title:
--   Lemma 6, randomized rounding — Pr(d(s_i|P, x) ≥ d0 + ε′|P| − d(s_i|Q, s′|Q) for some i) ≤ n·exp(−ε′²|P|/3) ≤ n^{−1/3}
-- statement:
--   Let $P$ be a finite set of positions, $a_1,\dots,a_n:P\to\Sigma$ strings (the restrictions $s_i|_P$), $b_1,\dots,b_n$ real offsets, and $\bar x_{j,a}\ge0$ ($j\in P$, $a\in\Sigma$) with $\sum_{a}\bar x_{j,a}=1$ for every $j$ and, for a real $D$,
--   $$\sum_{j\in P}\sum_{a\in\Sigma}\chi(a_i[j],a)\,\bar x_{j,a}\le D-b_i\qquad(i=1,\dots,n),$$
--   where $\chi(a',a)=0$ if $a'=a$ and $1$ otherwise. Round independently for each $j$: $x_j=a$ with probability $\bar x_{j,a}$. Then for every $\varepsilon'>0$
--
--   $$\Pr\big(d(a_i,x)\ge D+\varepsilon'|P|-b_i\ \text{for at least one } i\big)\ \le\ n\exp\Big(-\tfrac13\varepsilon'^2|P|\Big),$$
--
--   and if $|P|\ge(4\ln n)/\varepsilon'^2$ then $n\exp(-\frac13\varepsilon'^2|P|)\le n^{-1/3}$.
--
--   In the paper $\bar x$ is an optimal fractional solution of the LP relaxation (6), $D=d_0\ge\bar d$ and $b_i=d(s_i|_Q,s'|_Q)$. This is the randomized half of "the method provided in the proof of Lemma 6", which Figure 3 step 1(c)(ii) uses to solve problem (8) within error $\varepsilon|P|$.
--
--   Differences from the source:
--
--   - generalization: x̄ an optimal solution of (6) with cost d̄ ≤ d0, offsets d(s_i|Q, s′|Q), bound with d0 → any fractional x̄ with Σ_j Σ_a χ x̄ ≤ D − b_i for a real D, any real offsets b_i; reason: the argument uses only (7), E[d(s_i|P, x)] ≤ D − b_i; the paper's case is D = d0
--   - reading: "Independently for each 0 ≤ j ≤ |P|" → independently for each position j of P; reason: P has |P| positions 1, …, |P|; j = 0 is a slip
--   - encoding: the rounding: x_{j,a} = 1 with probability x̄_{j,a} → law of x : P → Σ is Measure.pi of Σ_a x̄_{j,a}·δ_a; reason: same law
-- source:
--   Li, Ma & Wang, On the Closest String and Substring Problems, arXiv:cs/0002012v1, p. 6, proof of Lemma 6 (rounding of the LP (6) and its failure probability)

import Mathlib

namespace ClosestString.PTAS

open MeasureTheory

/-- **Lemma 6, the rounding bound** (proof of Lemma 6, Li, Ma & Wang, arXiv:cs/0002012v1, p. 6):
let `ι` be a finite position set (the paper's `P`), `a_1, …, a_n : ι → A` (the `s_i|P`), offsets
`b_i`, and `x̄ : ι → A → ℝ` a fractional solution (`x̄ ≥ 0`, `Σ_a x̄_{j,a} = 1`) with
`Σ_j Σ_a χ(a_i[j], a) x̄_{j,a} ≤ D − b_i` for every `i`. Round independently at each position
(`x_j = a` with probability `x̄_{j,a}`). Then for every `ε′ > 0`,
`Pr(d(a_i, x) ≥ D + ε′|ι| − b_i for at least one i) ≤ n exp(−ε′²|ι|/3)`; and if
`|ι| ≥ (4 ln n)/ε′²`, then `n exp(−ε′²|ι|/3) ≤ n^{−1/3}`. -/
theorem lemma_6_rounding {A : Type*} [Fintype A] [DecidableEq A] [MeasurableSpace A]
    [DiscreteMeasurableSpace A] {ι : Type*} [Fintype ι] {n : ℕ} (a : Fin n → ι → A)
    (b : Fin n → ℝ) (xbar : ι → A → ℝ) (hx0 : ∀ j c, 0 ≤ xbar j c) (hx1 : ∀ j, ∑ c, xbar j c = 1)
    (D : ℝ) (hLP : ∀ i, ∑ j, ∑ c, (if a i j = c then (0 : ℝ) else 1) * xbar j c ≤ D - b i)
    (ε' : ℝ) (hε' : 0 < ε') :
    Measure.pi (fun j : ι => ∑ c : A, ENNReal.ofReal (xbar j c) • Measure.dirac c)
        {x | ∃ i, D + ε' * Fintype.card ι - b i ≤ (hammingDist (a i) x : ℝ)}
        ≤ ENNReal.ofReal (n * Real.exp (-(1 / 3) * ε' ^ 2 * Fintype.card ι)) ∧
      (4 * Real.log n / ε' ^ 2 ≤ Fintype.card ι →
        (n : ℝ) * Real.exp (-(1 / 3) * ε' ^ 2 * Fintype.card ι) ≤ (n : ℝ) ^ (-(1 / 3 : ℝ))) := by sorry

end ClosestString.PTAS
