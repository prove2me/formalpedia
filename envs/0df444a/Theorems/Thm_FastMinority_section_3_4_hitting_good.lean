-- Prove2me | Theorems.Thm_FastMinority_section_3_4_hitting_good
-- name    : FastMinority.section_3_4_hitting_good
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:08:09.263355+00:00
-- url     : https://prove2.me/theorems/a9169f01-b430-4c7e-8683-3ea7d82cd48d
-- title:
--   Section 3.4 — $\mathcal H^+$ is reached within $\lceil C'\log^2 n/\log k\rceil$ updates w.p. $\ge1/2$
-- statement:
--   Let $X$ be the minority-size chain of MINORITY with $n$ agents and odd sample size $k=\Theta(\log^2 n)$. For a suitable fixed constant $b>0$ (on the page, the $b$ of Proposition 3.7) and a suitable constant $C'>0$, from an arbitrary initial state, $\mathcal H^+$ is reached within
--   $$
--   T_{\mathcal H^+}=\Big\lceil C'\,\frac{\log^2 n}{\log k}\Big\rceil
--   $$
--   updates with probability at least $1/2$, for all sufficiently large $n$:
--   $\Pr[\tau_{\mathcal H^+}>T_{\mathcal H^+}]\le1/2$ with $\tau_{\mathcal H^+}=\inf\{t\ge0:X_t\in\mathcal H^+\}$.
--
--   This combines Lemma 3.1, Proposition 3.3 and Proposition 3.7 into the worst-case hitting time of $\mathcal H^+$.
--
--   **Formalization Note** Here $k=\Theta(\log^2 n)$ is read as the band $a(\ln n)^2\le k\le A(\ln n)^2$ for arbitrary constants $0<a\le A$; all other constants are chosen after $a,A$ and before $n$, $k$ and the initial state.
--
--   Differences from the source:
--   - reading: k = Θ(log² n), for sufficiently large n → ∀ 0 < a ≤ A, then the statement's constants and N, then ∀ n ≥ N and every odd k with a(ln n)² ≤ k ≤ A(ln n)²; reason: Θ is a pair of band constants fixed first; constants depending on n or k would make the statement trivial
--   - encoding: from an arbitrary state → every initial state x with 2x ≤ n; reason: the state space is {0, …, ⌊n/2⌋}
--   - reading: H⁺ with H both the good set (3.1) and the interval [M′+1, R′−1], with M′ and R′ undefined → H⁺ = H ∪ {0} with H the good set (3.1); reason: M′ and R′ are never defined, and the page defines the attempts by (3.1)
--   - reading: b, the constant of Proposition 3.7 → ∃ b > 0 chosen after a, A and before n, k, x, not tied to the b of that proposition; reason: the page gives b only as a suitable fixed constant, and H⁺ grows with b, so a valid b stays valid for every larger b
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Section 3.4, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_MinorityDynamics_Chain
import Definitions.Def_MinorityDynamics_Kernel
import Definitions.Def_FastMinority_goodPlus

set_option autoImplicit false

open Classical

namespace FastMinority

/-- **Hitting `𝓗⁺` with probability at least `1/2`** (Section 3.4, Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), p.13 = PDF p.15): "for a
suitable constant `C′`, `𝓗⁺` is reached within `T_{𝓗⁺} = ⌈C′ log² n / log k⌉` updates with probability
at least `1/2`", from an arbitrary state ("the worst-case hitting time (from an arbitrary state) of
`𝓗⁺`").

**Formalization Note** `k = Θ(log² n)` is read as the band `a (ln n)² ≤ k ≤ A (ln n)²` for arbitrary constants `0 < a ≤ A`, chosen first; every other constant is chosen after them and before `n`, `k` and the initial state. `b` is a suitable fixed constant (on the page, the one of Proposition 3.7), chosen after `a, A`; the statement does not tie it to that proposition's `b`.
`Pr(τ_{𝓗⁺} > t)` is `avoidProb … t x`. -/
theorem section_3_4_hitting_good :
    ∀ a A : ℝ, 0 < a → a ≤ A → ∃ b : ℝ, 0 < b ∧ ∃ C' : ℝ, 0 < C' ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ k : ℕ, Odd k → a * Real.log n ^ 2 ≤ k → (k : ℝ) ≤ A * Real.log n ^ 2 →
      ∀ x : Fin (n + 1), 2 * (x : ℕ) ≤ n →
      MinorityDynamics.avoidProb (MinorityDynamics.actualKernel n k) (goodPlus n k b)
          ⌈C' * Real.log n ^ 2 / Real.log k⌉₊ x ≤ 1 / 2 := by sorry

end FastMinority
