-- Prove2me | Theorems.Thm_FastMinority_lemma_3_5
-- name    : FastMinority.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:05:30.26071+00:00
-- url     : https://prove2.me/theorems/13d95470-d3e7-47eb-bf8e-3a388a57a393
-- title:
--   Lemma 3.5 — the lower region is left within $\lceil\log L/\log(k/2)\rceil$ rounds w.p. $\ge1-n^{-\gamma}$
-- statement:
--   Let $X$ be the minority-size chain of MINORITY with $n$ agents and odd sample size $k=\Theta(\log^2 n)$, let $L=\lceil n/(4k)\rceil$ and
--   $\tau_L=\inf\{t\ge0: X_t=0\ \text{or}\ X_t\ge L\}$. For every fixed $\gamma>0$ and all sufficiently large $n$, from every initial state,
--   $$
--   \Pr\Big[\tau_L>\Big\lceil\frac{\log L}{\log(k/2)}\Big\rceil\Big]\le n^{-\gamma}.
--   $$
--
--   The lower region is left after $O(\log n/\log k)$ rounds, w.h.p.; this is one of the three excursion bounds behind Proposition 3.3.
--
--   **Formalization Note** Here $k=\Theta(\log^2 n)$ is read as the band $a(\ln n)^2\le k\le A(\ln n)^2$ for arbitrary constants $0<a\le A$; all other constants are chosen after $a,A$ and before $n$, $k$ and the initial state. The chain's step is the published `actualKernel`; logarithms are natural.
--
--   Differences from the source:
--   - reading: k = Θ(log² n), for sufficiently large n → ∀ 0 < a ≤ A, then the statement's constants and N, then ∀ n ≥ N and every odd k with a(ln n)² ≤ k ≤ A(ln n)²; reason: Θ is a pair of band constants fixed first; constants depending on n or k would make the statement trivial
--   - reading: initial state not named (the proof conditions on X_t ∈ [1, L)) → every initial state x with 2x ≤ n; reason: for x ∉ [1, L − 1], τ_L = 0 and the bound is immediate; the uniform reading is the stronger one
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Lemma 3.5, p.9 (PDF p.11); proof pp.19–20 (PDF pp.21–22)

import Mathlib
import Definitions.Def_MinorityDynamics_Chain
import Definitions.Def_MinorityDynamics_Kernel
import Definitions.Def_FastMinority_lowThr

set_option autoImplicit false

open Classical

namespace FastMinority

/-- **Lemma 3.5** (Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), p.9 = PDF p.11; proof pp.19–20 = PDF pp.21–22): with
`τ_L = inf{t ≥ 0 : X_t = 0 or X_t ≥ L}`, for every fixed `γ > 0` and sufficiently large `n`,
`Pr[τ_L > ⌈log L / log(k/2)⌉] ≤ n^{−γ}`.

**Formalization Note** `k = Θ(log² n)` is read as the band `a (ln n)² ≤ k ≤ A (ln n)²` for arbitrary constants `0 < a ≤ A`, chosen first; every other constant is chosen after them and before `n`, `k` and the initial state. The chain's step is the published `actualKernel n k`; `Pr(τ_L > t)`
is `avoidProb … t x`. The initial state is any `x` with `2x ≤ n` (for `x ∉ [1, L − 1]`, `τ_L = 0`). -/
theorem lemma_3_5 :
    ∀ a A : ℝ, 0 < a → a ≤ A → ∀ γ : ℝ, 0 < γ → ∃ N : ℕ, ∀ n ≥ N, ∀ k : ℕ, Odd k → a * Real.log n ^ 2 ≤ k → (k : ℝ) ≤ A * Real.log n ^ 2 →
      ∀ x : Fin (n + 1), 2 * (x : ℕ) ≤ n →
      MinorityDynamics.avoidProb (MinorityDynamics.actualKernel n k)
          {s | (s : ℕ) = 0 ∨ lowThr n k ≤ (s : ℕ)}
          ⌈Real.log (lowThr n k) / Real.log ((k : ℝ) / 2)⌉₊ x ≤ (n : ℝ) ^ (-γ) := by sorry

end FastMinority
