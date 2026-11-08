-- Prove2me | Theorems.Thm_EuclidDiamStream_theorem_2
-- name    : EuclidDiamStream.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:48.860918+00:00
-- url     : https://prove2.me/theorems/369776c7-454d-4fd4-a682-c57c328d4d8e
-- title:
--   Theorem 2 — linear sketches for the $(r,c,n)$-diameter problem need dimension $n^{\tilde\Omega(1/c^2)}$
-- statement:
--   For $n\in\mathbb N$, any $c>1$ and sufficiently small constant $\delta>0$, the scale $r=\sqrt d/(c\sqrt3)>0$ and the distribution $\mathcal D$ of Definition 3.1 satisfy the following.
--   1. $\mathrm{diam}_{r,c,n}(v)\in\{0,1\}$ with high probability over $v\sim\mathcal D$: for every $\varepsilon>0$ the probability of $*$ is at most $\varepsilon$ once $n$ is large, uniformly in $c,\Delta,P,U$.
--   2. There are absolute constants $\delta_0,C>0$ and $n_0$ such that for $\delta\le\delta_0$, $n\ge n_0$ and every $\lambda$, there is a setting of $P,U\ge1$ for which every $(s,\lambda)$-linear sketch $(T,\mathrm{Dec})$ with
--   $$\Pr_{v\sim\mathcal D}\big[\mathrm{Dec}(Tv)=\mathrm{diam}_{r,c,n}(v)\big]\ge1-\delta$$
--   has
--   $$s\ge n^{C/(c^2\log_2(2c))}.$$
--
--   This is the sketching form of the lower bound, and the streaming form follows from it.
--
--   Differences from the source:
--   - reading: "there exists r > 0 and a distribution D" → r = hardScale n c with 0 < r, D = hardDist n c Δ P U; reason: the proof's witnesses (Def. 3.1, Lemma 3.9), and the explicit form implies the existential
--   - reading: s = n^{Ω̃(1/c²)} → s ≥ n^{C/(c²·log₂(2c))} with absolute C; reason: the proof gives n^{Ω(1/(c² log c))} (p.8); log₂(2c) is the form uniform as c → 1⁺, where log c vanishes
--   - reading: "for n, λ ∈ ℕ, any c > 1, and sufficiently small constant δ > 0" → δ₀, C, n₀ absolute, before δ, c, n, Δ, λ; n ≥ n₀; reason: a small n carries no content in an Ω̃ statement; absolute constants are the strongest order
--   - reading: "with high probability" → for every ε > 0 the probability of ∗ is ≤ ε for n ≥ n₁(ε), uniformly in c > 1, Δ ≥ 1, P, U; reason: 1 − o(1) as on p.8; uniform because Pr[∗] ≤ Pr[Ham(x,y) < d/3] and d(n,c) → ∞ uniformly in c
--   - reading: r = 2√τ = √d/(c√3) (Def. 3.1, p.7) → r = hardScale n c = √d/(c√3); reason: the two printed values agree only when 12c² divides d, and 2√τ = 0 at τ = 0 violates r > 0; Lemma 3.9, p.13, fixes √d/(c√3)
--   - encoding: D draws x, y, v_y, then v_z on B(x,τ), with positive integers P, U → one uniform draw on Cube d × Cube d × Bool × (Cube d → Fin (PU)), mapped by hardVec, with P, U : ℕ+; the ball draw determines v_y when y ∈ B(x,τ); reason: the same law, following the order of the page
--   - encoding: Dec(Tv) ≠ diam_{r,c,n}(v), with diam_{r,c,n}(v) ∈ {0,1,∗} → some (Dec (T v)) ≠ diamGap r c n v; reason: Dec outputs a bit, so ∗ counts as an error, as footnote 11 (p.20) treats it
-- source:
--   Padaki, Singal, Waingarten, A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.7, Theorem 2; proof p.8

import Mathlib
import Definitions.Def_EuclidDiamStream_hardDist
import Definitions.Def_EuclidDiamStream_IsLinearSketch

namespace EuclidDiamStream

/-- Theorem 2 of Padaki, Singal, Waingarten, *A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams*, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.7: for `n, λ ∈ ℕ`, any `c > 1` and sufficiently small constant `δ > 0`, there are `r > 0`
and a distribution `D` on frequency vectors `v` such that `diam_{r,c,n}(v) ∈ {0,1}` with high probability, and
every `(s,λ)`-linear sketch `(T, Dec)` with `Pr_{v∼D}[Dec(Tv) = diam_{r,c,n}(v)] ≥ 1 − δ` has `s = n^{Ω̃(1/c²)}`.

**Formalization Note.** `r` and `D` are given explicitly, as `hardScale n c` (with `r > 0`, the first clause) and
`hardDist n c Δ P U`. "With high probability" is `1 − o(1)` as `n → ∞`, uniformly in `c, Δ, P, U`, the second
clause. `Ω̃` is read as the exponent `C/(c²·log₂(2c))`, with `δ₀, C, n₀` absolute and before `δ, c, n, Δ, λ`. The
form `log₂(2c)` is uniform as `c → 1⁺`, where `log c` would vanish. `P, U` are chosen after `λ` and before `s`, as
in the proof (p.8). -/
theorem theorem_2 :
    (∀ (n : ℕ) (c : ℝ), 2 ≤ n → 1 < c → 0 < hardScale n c) ∧
    (∀ ε : ℝ, 0 < ε → ∃ n₁ : ℕ, ∀ (n : ℕ) (c : ℝ) (Δ : ℕ) (P U : ℕ+), n₁ ≤ n → 1 < c → 1 ≤ Δ →
      (hardDist n c Δ P U).toOuterMeasure {v | diamGap (hardScale n c) c n v = none} ≤
        ENNReal.ofReal ε) ∧
    (∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ,
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ c : ℝ, 1 < c → ∀ n : ℕ, n₀ ≤ n → ∀ Δ : ℕ, 1 ≤ Δ →
      ∀ lam : ℕ, ∃ P U : ℕ+,
        ∀ (s : ℕ) (T : Matrix (Fin s) (Point (hardDim n c) Δ) ℤ) (Dec : (Fin s → ℤ) → Bool),
          IsLinearSketch T lam → ENNReal.ofReal (1 - δ) ≤ hardSuccess n c Δ P U T Dec →
          (n : ℝ) ^ (C / (c ^ 2 * Real.logb 2 (2 * c))) ≤ (s : ℝ)) := by sorry

end EuclidDiamStream
