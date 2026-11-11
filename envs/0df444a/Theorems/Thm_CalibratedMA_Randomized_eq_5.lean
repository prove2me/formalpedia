-- Prove2me | Theorems.Thm_CalibratedMA_Randomized_eq_5
-- name    : CalibratedMA.Randomized.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:25:30.609751+00:00
-- url     : https://prove2.me/theorems/172a59c1-1afa-4a7b-a225-cc40b947b0da
-- title:
--   Section 3.4, Eq. (5) — size of the lifted class: log |A_{M,ρ}| ≤ C M log(e/ρ)
-- statement:
--   Let $\rho>0$ with $1/\rho$ an integer, $K_\rho=|\Lambda_\rho|=1/\rho+1$, and let $M\ge1$ be an integer. The lifted test class $\mathcal A_{M,\rho}$ of Section 3.4 satisfies the counting bound
--   $$|\mathcal A_{M,\rho}|\le\sum_{L=1}^M\binom{K_\rho}{L+1}2^{L+1}\le (M+1)(2K_\rho)^{M+1},$$
--   and, for a universal constant $C$,
--   $$\log|\mathcal A_{M,\rho}|\le C\,M\log(e/\rho).\tag{5}$$
--
--   This bound makes the online learner's guarantee (Lemma 3.1) over $\Phi_{\mathcal G,\mathcal A}$ cost only $O(m\log(e/\rho))$ in the logarithm, which yields the $(\log(2n/\delta)/n)^{2/5}$ term of Theorem 4.1.
--
--   **Formalization Note.** $\rho=1/K$ with $K\ge1$ a natural number, so $K_\rho=K+1$ and $e/\rho$ is written `exp 1 / (1/K)`. $|\mathcal A_{M,\rho}|$ is the cardinality of the `Finset` of distinct lifted functions. $C$ is quantified before $K$ and $M$.
--
--   Differences from the source:
--   - encoding: $\rho>0$ with $1/\rho$ an integer → $K\in\mathbb N$, $K\ge1$, $\rho=1/K$; reason: same instances.
--   - encoding: $\mathcal A_{M,\rho}$ as a class of functions on $[0,1]$ → a `Finset (ℝ → ℝ)` of lifts extended to $\mathbb R$ by clamping the score to $[0,1]$; reason: functions that agree on $[0,1]$ have the same extension, so the cardinality is unchanged.
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026), p. 17, Section 3.4, counting display and Eq. (5)

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_Rounding

namespace CalibratedMA.Randomized

/-- Section 3.4, the counting bound and Eq. (5) (p. 17): with `ρ = 1/K`, `K_ρ = |Λ_ρ| = K + 1`,
`|A_{M,ρ}| ≤ Σ_{L=1}^M (K_ρ choose L+1) 2^{L+1} ≤ (M + 1)(2K_ρ)^{M+1}` and `log |A_{M,ρ}| ≤ C M log(e/ρ)` for a universal `C`. -/
theorem eq_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ K M : ℕ, 1 ≤ K → 1 ≤ M →
      (liftedClass K M).card ≤
        ∑ L ∈ Finset.Icc 1 M, Nat.choose (K + 1) (L + 1) * 2 ^ (L + 1) ∧
      (∑ L ∈ Finset.Icc 1 M, Nat.choose (K + 1) (L + 1) * 2 ^ (L + 1)) ≤
        (M + 1) * (2 * (K + 1)) ^ (M + 1) ∧
      Real.log (liftedClass K M).card ≤ C * M * Real.log (Real.exp 1 / (1 / (K : ℝ))) := by sorry

end CalibratedMA.Randomized
