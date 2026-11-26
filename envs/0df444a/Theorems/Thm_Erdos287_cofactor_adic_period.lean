-- Prove2me | Theorems.Thm_Erdos287_cofactor_adic_period
-- name    : Erdos287.cofactor_adic_period
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T11:51:25.437741+00:00
-- url     : https://prove2.me/theorems/6bd7b1d1-001b-5883-851e-ba1c483e2d1d
-- title:
--   Periodicity of the full prime-adic condition on cofactor patterns
-- statement:
--   Suppose the cofactors of the selected multiples of $p^e$ in a positive denominator set of reciprocal sum one are $c+T$. The sum $S(c)=\sum_{d\in T}1/(c+d)$ has $p$-adic valuation at least one. More generally, if the offset diameter is less than $p^{h+1}$, the condition $v_p(S(c))\ge1$ on positive $c$ is periodic modulo $p^{2h+1}$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.cofactor_adic_period (p : ℕ) (hp : p.Prime) :
    (∀ (D T : Finset ℕ) (e c : ℕ), 1 ≤ e → 0 < c →
      (∀ n ∈ D, 0 < n) → (∑ n ∈ D, (1 : ℚ) / n = 1) →
      T.image (fun d => (c + d) * p ^ e) = D.filter (fun n => p ^ e ∣ n) →
      padicNorm p (∑ d ∈ T, (1 : ℚ) / ((c + d : ℕ) : ℚ)) ≤ (p : ℚ)⁻¹) ∧
    ∀ (T : Finset ℕ) (h c c' : ℕ), 0 < c → 0 < c' →
      (∀ a ∈ T, ∀ b ∈ T, a < b + p ^ (h + 1)) →
      c ≡ c' [MOD p ^ (2 * h + 1)] →
      (padicNorm p (∑ d ∈ T, (1 : ℚ) / ((c + d : ℕ) : ℚ)) ≤ (p : ℚ)⁻¹ ↔
       padicNorm p (∑ d ∈ T, (1 : ℚ) / ((c' + d : ℕ) : ℚ)) ≤ (p : ℚ)⁻¹) := by sorry
