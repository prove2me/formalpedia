-- Prove2me | Theorems.Thm_Disjunctive_MonoidalStrengthening_monoidal_strengthening_validity
-- name    : Disjunctive.MonoidalStrengthening.monoidal_strengthening_validity
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T17:03:15.329039+00:00
-- url     : https://prove2.me/theorems/3e221ea8-aebd-401f-8b5b-699d11226269
-- title:
--   Proposition 11.22 — validity of the monoidally-strengthened disjunction
-- statement:
--   This is Proposition 11.22 of Balas's *Disjunctive Programming*, the validity engine directly
--   cited by Theorem 11.23's proof ("by monoidal strengthening applied to (11.43) and Proposition
--   11.22..."), and hence, through Theorem 11.23's specialization, ultimately underlying the goal
--   theorem of this mission.
--
--   Let $x \ge 0$ be integer on $J_1$, satisfy the $q$-term disjunction $\bigvee_{i\in
--   Q}(\sum_j a_{ij}x_j \ge a_{i0})$, and satisfy the background lower bound $\sum_j a_{ij}x_j \ge
--   b_i$ for every $i \in Q$ simultaneously. Then, for **any** fixed choice of monoid elements
--   $m^j \in M$ ($j \in J_1$), $x$ also satisfies the strengthened disjunction
--   $$
--   \bigvee_{i\in Q}\Big(\sum_{j\in J_1}\big(a_{ij}+(a_{i0}-b_i)m^i_j\big)x_j +
--   \sum_{j\in J\setminus J_1} a_{ij}x_j \ge a_{i0}\Big).
--   $$
--
--   This is the mechanism by which monoidal strengthening is legitimate at all: it holds for
--   *every* monoid element, which is what licenses optimizing (taking the infimum) over the whole
--   monoid afterward, as Theorem 11.19/Theorem 11.23 both do.
--
--   **Formalization Note.** Unlike Theorem 11.19's `AlphaJStrengthened` (which optimizes over the
--   monoid via `sInf`), this proposition fixes an arbitrary `m` satisfying `hm_mem` and asserts
--   validity for that fixed choice — matching the proposition's own "any $x$ satisfying..." and
--   "for any fixed $m^j$" framing, and matching exactly how Theorem 11.23's proof uses it (first
--   for one explicit $m^1_j$, then for the minimizing $m^2_j$, then takes the pointwise minimum of
--   the two resulting valid coefficients).
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 179-180, Proposition 11.22

import Mathlib
import Definitions.Def_Disjunctive_MonoidalStrengthening_Basic

namespace Disjunctive.MonoidalStrengthening

/-- Proposition 11.22 (Balas §11.9, p. 179-180): any `x ≥ 0`, integer on `J₁`, satisfying the
`q`-term disjunction (11.38) `∨_i(Σ_j a_ij x_j ≥ a_i0)` and the background lower bound `Σ_j a_ij
x_j ≥ b_i` for every `i ∈ Q`, also satisfies the monoidally-strengthened disjunction (11.41), for
any fixed choice of `m^j ∈ M` (`j ∈ J₁`). -/
theorem monoidal_strengthening_validity {q n : ℕ}
    (a : Fin q → Fin n → ℝ) (a0 b : Fin q → ℝ) (J1 : Finset (Fin n))
    (m : Fin n → Fin q → ℤ) (hm_mem : ∀ j ∈ J1, (fun i => m j i) ∈ CutMonoid q)
    (x : Fin n → ℝ) (hx_nonneg : 0 ≤ x) (hx_int : ∀ j ∈ J1, ∃ k : ℤ, x j = (k : ℝ))
    (hx_lb : ∀ i, b i ≤ ∑ j, a i j * x j)
    (hx_disj : ∃ i, a0 i ≤ ∑ j, a i j * x j) :
    ∃ i, a0 i ≤ ∑ j ∈ J1, (a i j + (a0 i - b i) * (m j i : ℝ)) * x j +
      ∑ j ∈ Finset.univ \ J1, a i j * x j := by sorry

end Disjunctive.MonoidalStrengthening
