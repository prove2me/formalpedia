-- Prove2me | Theorems.Thm_FastMinority_lemma_5_18
-- name    : FastMinority.lemma_5_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:07:52.14837+00:00
-- url     : https://prove2.me/theorems/b001abe2-3440-4649-93ea-4fb7086ce798
-- title:
--   Lemma 5.18 — first core entry from $0<x=O(\log n)$: $\max_{j\in\mathcal C}p_j=o(k^2/n)$
-- statement:
--   Let $X$ be the minority-size chain of MINORITY with $n$ agents and odd sample size $k=\Theta(\log^2 n)$, let $D>2$, $b>0$, let $\tau=\inf\{t\ge0:X_t\in\mathcal C\}$ and fix $0<x=O(\log n)$. For each $j\in\mathcal C$ put $p_j=\Pr[\tau<\infty,\ X_\tau=j\mid X_0=x]$. Then
--   $$
--   \hat p:=\max_{j\in\mathcal C}p_j\in o\Big(\frac{k^2}{n}\Big):
--   $$
--   for every constant $c_0>0$ and every $\varepsilon>0$, for all sufficiently large $n$, every odd $k$ in the band, every $0<x\le c_0\ln n$ and every $j\in\mathcal C$, $p_j\le\varepsilon k^2/n$.
--
--   After a failed attempt at consensus the minority is $O(\log n)$, and from there no core state is hit with probability more than $o(k^2/n)$; this sharpens $p_{\max}$ in Lemma 3.1 for the high-probability clause of Theorem 1.1.
--
--   **Formalization Note** Here $k=\Theta(\log^2 n)$ is read as the band $a(\ln n)^2\le k\le A(\ln n)^2$ for arbitrary constants $0<a\le A$; all other constants are chosen after $a,A$ and before $n$, $k$ and the initial state. $p_j$ is the increasing limit of $\Pr[\tau\le T,X_\tau=j]$ (`hitWithin`), bounded for every horizon $T$. $\tau$ is the first hitting time of $\mathcal C$ by $X$ itself.
--
--   Differences from the source:
--   - reading: k = Θ(log² n), for sufficiently large n → ∀ 0 < a ≤ A, then the statement's constants and N, then ∀ n ≥ N and every odd k with a(ln n)² ≤ k ≤ A(ln n)²; reason: Θ is a pair of band constants fixed first; constants depending on n or k would make the statement trivial
--   - reading: regions L = [1, L−1], C = [L, M′], H = [M′+1, R′−1], U = [R′, ⌊n/2⌋] for a constant D > 2, with M′ ≤ M and R′ ≥ R undefined → H = good set (3.1), U = [R, ⌊n/2⌋], C = [L, R−1] \ H, for every D > 2; reason: M′ and R′ are never defined; the page says it is enough to work with M and R
--   - generalization: the fixed constant b of the definition of H → every b > 0; reason: specializes to the paper's b
--   - encoding: x = O(log n), p̂ ∈ o(k²/n) → ∀ c₀ > 0, ∀ ε > 0, ∃ N such that p_j ≤ ε k²/n for n ≥ N, odd k in the band, 0 < x ≤ c₀ ln n, j ∈ C; reason: the definitions of O and o, uniform in k, x and j
--   - encoding: Pr[τ < ∞, X_τ = j] → Pr[τ ≤ T, X_τ = j] ≤ bound for every horizon T; reason: the probability is the increasing limit over T
--   - reading: τ = inf{t ≥ 0 : X_t ∈ C} (the proof's remark that trajectories reaching H⁺ first have τ = ∞) → τ the first hitting time of C by X itself, not stopped at H⁺; reason: the literal definition; it is the stronger reading (more trajectories count toward p_j)
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Lemma 5.18, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_MinorityDynamics_Chain
import Definitions.Def_FastMinority_coreRegion
import Definitions.Def_FastMinority_hitWithin

set_option autoImplicit false

open Classical

namespace FastMinority

/-- **Lemma 5.18** (Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), p.35 = PDF p.37): let `τ = inf{t ≥ 0 : X_t ∈ 𝓒}` and fix
`0 < x = O(log n)`. For each `j ∈ 𝓒` put `p_j = Pr[τ < ∞, X_τ = j | X₀ = x]`. Then
`p̂ := max_{j ∈ 𝓒} p_j ∈ o(k²/n)`.

**Formalization Note** `k = Θ(log² n)` is read as the band `a (ln n)² ≤ k ≤ A (ln n)²` for arbitrary constants `0 < a ≤ A`, chosen first; every other constant is chosen after them and before `n`, `k` and the initial state. The region constant `D > 2` and the constant `b` of `𝓗` are
arbitrary. `x = O(log n)` is `x ≤ c₀ ln n` for an arbitrary constant `c₀ > 0`; `o(k²/n)` is
"for every `ε > 0`, `≤ ε k²/n` for large `n`". `Pr(τ < ∞, X_τ = j)` is the increasing limit of
`hitWithin … T x`, bounded for every horizon `T`. `τ` is the first hitting time of `𝓒` by `X` itself. -/
theorem lemma_5_18 :
    ∀ a A : ℝ, 0 < a → a ≤ A → ∀ D : ℝ, 2 < D → ∀ b : ℝ, 0 < b → ∀ c₀ : ℝ, 0 < c₀ →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ k : ℕ, Odd k → a * Real.log n ^ 2 ≤ k → (k : ℝ) ≤ A * Real.log n ^ 2 →
      ∀ x : Fin (n + 1), 0 < (x : ℕ) → ((x : ℕ) : ℝ) ≤ c₀ * Real.log n →
      ∀ j ∈ coreRegion n k D b, ∀ T : ℕ,
      hitWithin (MinorityDynamics.actualKernel n k) (coreRegion n k D b) {j} T x ≤
        ε * (k : ℝ) ^ 2 / n := by sorry

end FastMinority
