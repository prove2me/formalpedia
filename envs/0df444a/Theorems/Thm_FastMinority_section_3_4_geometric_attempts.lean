-- Prove2me | Theorems.Thm_FastMinority_section_3_4_geometric_attempts
-- name    : FastMinority.section_3_4_geometric_attempts
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:04:41.608207+00:00
-- url     : https://prove2.me/theorems/0880e06b-70b5-477c-bb72-dd86179a85b3
-- title:
--   Section 3.4 — $\Pr[T>\ell(T_{\mathcal H^+}+1)]\le(1-\delta/2)^\ell$, $\delta=e^{-8b}$
-- statement:
--   Let $X$ be the minority-size chain of MINORITY with $n$ agents and odd sample size $k=\Theta(\log^2 n)$, $T=\inf\{t\ge0:X_t=0\}$ its convergence time, $\delta=e^{-8b}$ and $T_{\mathcal H^+}=\lceil C'\log^2 n/\log k\rceil$. For suitable constants $b>0$ and $C'>0$, for all sufficiently large $n$, from every initial state,
--   $$
--   \Pr\big[T>\ell\,(T_{\mathcal H^+}+1)\big]\le(1-\delta/2)^\ell\qquad\text{for every integer }\ell\ge0.
--   $$
--
--   Summing over $\ell$ gives $\mathbb E[T]\le2(T_{\mathcal H^+}+1)/\delta=O(\log^2 n/\log k)$, the expectation clause of Theorem 1.1 for the chain.
--
--   **Formalization Note** Here $k=\Theta(\log^2 n)$ is read as the band $a(\ln n)^2\le k\le A(\ln n)^2$ for arbitrary constants $0<a\le A$; all other constants are chosen after $a,A$ and before $n$, $k$ and the initial state.
--
--   Differences from the source:
--   - reading: k = Θ(log² n), for sufficiently large n → ∀ 0 < a ≤ A, then the statement's constants and N, then ∀ n ≥ N and every odd k with a(ln n)² ≤ k ≤ A(ln n)²; reason: Θ is a pair of band constants fixed first; constants depending on n or k would make the statement trivial
--   - encoding: from every initial state (implicit) → every initial state x with 2x ≤ n; reason: the state space is {0, …, ⌊n/2⌋}
--   - reading: δ = e^{−8b} and T_{H⁺} with the b of Proposition 3.7 and the C′ of the hitting bound → ∃ b > 0, ∃ C′ > 0 chosen after a, A and before n, k, x, not tied to those of the other items; reason: the page gives b and C′ only as suitable fixed constants
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Section 3.4, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_MinorityDynamics_Chain
import Definitions.Def_MinorityDynamics_Kernel

set_option autoImplicit false

open Classical

namespace FastMinority

/-- **Geometric attempts** (Section 3.4, Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), p.14 = PDF p.16): with `δ = e^{−8b}` and
`T_{𝓗⁺} = ⌈C′ log² n / log k⌉`, "`Pr[T > ℓ(T_{𝓗⁺} + 1)] ≤ (1 − δ/2)^ℓ` for every integer `ℓ ≥ 0`",
where `T = inf{t ≥ 0 : X_t = 0}` is the convergence time of `X`.

**Formalization Note** `k = Θ(log² n)` is read as the band `a (ln n)² ≤ k ≤ A (ln n)²` for arbitrary constants `0 < a ≤ A`, chosen first; every other constant is chosen after them and before `n`, `k` and the initial state. `b` (through `δ`) and `C′` are chosen after `a, A` and before `n`,
`k` and the initial state `x` (any `x` with `2x ≤ n`). `Pr(T > t)` is `avoidProb … {0} t x`. -/
theorem section_3_4_geometric_attempts :
    ∀ a A : ℝ, 0 < a → a ≤ A → ∃ b : ℝ, 0 < b ∧ ∃ C' : ℝ, 0 < C' ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ k : ℕ, Odd k → a * Real.log n ^ 2 ≤ k → (k : ℝ) ≤ A * Real.log n ^ 2 →
      ∀ x : Fin (n + 1), 2 * (x : ℕ) ≤ n → ∀ ℓ : ℕ,
      MinorityDynamics.avoidProb (MinorityDynamics.actualKernel n k) {0}
          (ℓ * (⌈C' * Real.log n ^ 2 / Real.log k⌉₊ + 1)) x ≤
        (1 - Real.exp (-8 * b) / 2) ^ ℓ := by sorry

end FastMinority
