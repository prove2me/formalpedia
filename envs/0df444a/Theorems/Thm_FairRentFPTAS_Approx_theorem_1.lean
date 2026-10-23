-- Prove2me | Theorems.Thm_FairRentFPTAS_Approx_theorem_1
-- name    : FairRentFPTAS.Approx.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:53.571611+00:00
-- url     : https://prove2.me/theorems/d2c47e48-ddcf-4cb4-bf4d-6c024fb898b8
-- title:
--   Theorem 1, p. 9 — on instances with the powers-of-(1+ε) property, Algorithm 1 returns an envy-free solution after polynomially many iterations
-- statement:
--   There is a constant $c\in\mathbb N$ such that the following holds. Let $J$ be a well-formed instance with $n\ge1$ agents, $\varepsilon>0$, all slopes of $J$ integer powers of $(1+\varepsilon)$, $\beta$ a bound on $|\log\lambda|$ over the slopes $\lambda$ of $J$, $\ell$ the total number of pieces of $J$, and $M$ a threshold with $v_a(r,M)<v_a(r',0)$ for all $a,r,r'$. Then
--   1. Algorithm 1 can be run on $J$ until it halts (some run reaches a price vector with a nonpositive entry);
--   2. every run has at most
--   $$T\ \le\ c\,\big(n+\ell+\beta+1/\varepsilon+1\big)^{c}$$
--   iterations, whatever Step 2 solution, maximum-weight matchings and LP optima are chosen;
--   3. every halted run outputs nonnegative rents $p^T\ge0$ such that $(\pi^T,p^T)$ is an envy-free solution of $J$ itself.
--
--   This is the exact algorithm for structured instances; Theorem 2 applies it to the rounded instance.
--
--   **Formalization Note** Only the number of while-iterations is bounded; the cost of one iteration (a maximum-weight matching and a linear program) is not formalized. The constant $c$ is chosen before the instance.
-- source:
--   Arunachaleswaran, Barman & Rathi, Fully Polynomial-Time Approximation Schemes for Fair Rent Division, arXiv:1807.04163v1, p. 9, Theorem 1 (proof pp. 13–14)

import Mathlib
import Definitions.Def_FairRentFPTAS_Approx_Model

namespace FairRentFPTAS.Approx

/-- Theorem 1, p. 9 (proof pp. 13–14): for instances whose slopes are integer powers of
`(1+ε)`, Algorithm 1 can be run to completion, every run stops after a number of iterations
bounded by a fixed polynomial in `n`, the number `ℓ` of pieces, the slope bound `β` and `1/ε`,
and every output is an envy-free solution of the instance with nonnegative rents. -/
theorem theorem_1 : ∃ c : ℕ, ∀ (n : ℕ) (J : Instance n) (ε β M : ℝ),
    1 ≤ n → Standing J → 0 < ε → PowersProp ε J →
    (∀ a r, ∀ e ∈ (J.v a r).pieces, |Real.log e.2| ≤ β) →
    IsThreshold J M →
    (∃ (T : ℕ) (π : ℕ → Equiv.Perm (Fin n)) (p : ℕ → Fin n → ℝ),
        IsRun J M T π p ∧ Halted p T) ∧
    (∀ (T : ℕ) (π : ℕ → Equiv.Perm (Fin n)) (p : ℕ → Fin n → ℝ), IsRun J M T π p →
        (T : ℝ) ≤ c * ((n : ℝ) + totalPieces J + β + 1 / ε + 1) ^ c) ∧
    (∀ (T : ℕ) (π : ℕ → Equiv.Perm (Fin n)) (p : ℕ → Fin n → ℝ), IsRun J M T π p →
        Halted p T → (∀ r, 0 ≤ p T r) ∧ IsEF J (π T) (p T)) := by sorry

end FairRentFPTAS.Approx
