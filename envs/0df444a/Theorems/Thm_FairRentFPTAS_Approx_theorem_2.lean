-- Prove2me | Theorems.Thm_FairRentFPTAS_Approx_theorem_2
-- name    : FairRentFPTAS.Approx.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:51.455298+00:00
-- url     : https://prove2.me/theorems/6607168c-c19e-43b3-9a47-b80411e98ebe
-- title:
--   Theorem 2, p. 9 — Algorithm 1 on the slope-rounded instance halts within poly(n, ℓ, β, 1/ε) iterations and returns an ε-EF solution with nonnegative rents
-- statement:
--   There is a constant $c\in\mathbb N$ such that the following holds. Let $\mathcal I$ be a rent-division instance with $n\ge1$ agents and continuous, strictly decreasing piecewise-linear utilities, with $\ell$ pieces in total and $|\log\lambda|\le\beta$ for every slope $\lambda$. Let $0<\varepsilon<1$, let $\bar{\mathcal I}$ be the slope-rounded instance of §5, and let $M$ satisfy $\bar v_a(r,M)<\bar v_a(r',0)$ for all $a,r,r'$. Then, for Algorithm 1 run on $\bar{\mathcal I}$ with threshold $M$:
--   1. some run halts;
--   2. every run, whatever Step 2 solution, maximum-weight matchings and LP optima it uses, has at most
--   $$T\ \le\ c\,\big(n+\ell+\beta+1/\varepsilon+1\big)^{c}$$
--   iterations;
--   3. every halted run outputs $(\pi^T,p^T)$ with $p^T\ge0$ that is an $\varepsilon$-EF solution of the original instance $\mathcal I$.
--
--   This is the paper's FPTAS for fair rent division: an approximately envy-free solution is obtained after a number of iterations polynomial in $1/\varepsilon$ and the input size.
--
--   **Formalization Note** Only the iteration count is bounded; the cost of one iteration (computing $\bar{\mathcal I}$ and $M$, a maximum-weight matching, a linear program) and the bit length of the input are not formalized, and $\beta$ (natural logarithm) stands in for the bit complexity of the slopes. $\varepsilon<1$ is the range of §5 and Lemma 9. The constant $c$ is chosen before the instance.
-- source:
--   Arunachaleswaran, Barman & Rathi, Fully Polynomial-Time Approximation Schemes for Fair Rent Division, arXiv:1807.04163v1, p. 9, Theorem 2 (restated p. 18)

import Mathlib
import Definitions.Def_FairRentFPTAS_Approx_Model

namespace FairRentFPTAS.Approx

/-- Theorem 2, p. 9 (restated p. 18): Algorithm 1 run on the slope-rounded instance `Ī`
can be run to completion, every run stops within a number of iterations bounded by a fixed
polynomial in `n`, the number `ℓ` of given pieces, the slope bound `β` and `1/ε`, and every
output has nonnegative rents and is an `ε`-EF solution of the original instance `I`. -/
theorem theorem_2 : ∃ c : ℕ, ∀ (n : ℕ) (I : Instance n) (ε β M : ℝ),
    1 ≤ n → Standing I → 0 < ε → ε < 1 →
    (∀ a r, ∀ e ∈ (I.v a r).pieces, |Real.log e.2| ≤ β) →
    IsThreshold (roundInst ε I) M →
    (∃ (T : ℕ) (π : ℕ → Equiv.Perm (Fin n)) (p : ℕ → Fin n → ℝ),
        IsRun (roundInst ε I) M T π p ∧ Halted p T) ∧
    (∀ (T : ℕ) (π : ℕ → Equiv.Perm (Fin n)) (p : ℕ → Fin n → ℝ), IsRun (roundInst ε I) M T π p →
        (T : ℝ) ≤ c * ((n : ℝ) + totalPieces I + β + 1 / ε + 1) ^ c) ∧
    (∀ (T : ℕ) (π : ℕ → Equiv.Perm (Fin n)) (p : ℕ → Fin n → ℝ), IsRun (roundInst ε I) M T π p →
        Halted p T → (∀ r, 0 ≤ p T r) ∧ IsEpsEF I ε (π T) (p T)) := by sorry

end FairRentFPTAS.Approx
