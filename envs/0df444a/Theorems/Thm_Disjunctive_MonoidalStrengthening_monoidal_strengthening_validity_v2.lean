-- Prove2me | Theorems.Thm_Disjunctive_MonoidalStrengthening_monoidal_strengthening_validity_v2
-- name    : Disjunctive.MonoidalStrengthening.monoidal_strengthening_validity_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:37.44099+00:00
-- url     : https://prove2.me/theorems/2fe329c6-abfc-4d07-b53f-159f8e7c85d3
-- title:
--   Proposition 11.22 — validity of the monoidally-strengthened disjunction (with $b_i \le a_{i0}$)
-- statement:
--   This is Proposition 11.22 of Balas's *Disjunctive Programming*, the validity engine behind monoidal cut strengthening.
--
--   Consider the $q$-term disjunction $\bigvee_{i\in Q}\big(\sum_j a_{ij}x_j \ge a_{i0}\big)$ together with background lower bounds $\sum_j a_{ij}x_j \ge b_i$ ($i\in Q$), where, as throughout the section, each bound does not exceed the corresponding right-hand side: $b_i \le a_{i0}$. Let $M := \{m\in\mathbb Z^q : \sum_{i} m_i \ge 0\}$ be the cut monoid and fix arbitrary $m^j \in M$ for $j\in J_1$.
--
--   If $x \ge 0$, $x_j\in\mathbb Z$ for $j\in J_1$, $x$ satisfies all background bounds and at least one term of the disjunction, then $x$ also satisfies the strengthened disjunction
--   $$
--   \bigvee_{i\in Q}\Big(\sum_{j\in J_1}\big(a_{ij}+(a_{i0}-b_i)\,m^j_i\big)x_j + \sum_{j\in J\setminus J_1} a_{ij}x_j \ge a_{i0}\Big).
--   $$
--
--   **Formalization Note.** The retired version omitted the standing assumption $b_i \le a_{i0}$; with $b_i > a_{i0}$ the factor $a_{i0}-b_i$ is negative and a positive monoid entry destroys validity ($q=n=1$, $a=a_0=1$, $b=3$, $m=1$, $x=3$). The new statement adds exactly this assumption (hypothesis `hb`) and is otherwise unchanged. The disjunction index set is `Fin q`, the variables `Fin n`; $m^j$ is only constrained (and only used) for $j \in J_1$.
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §11.9, p. 179-180, Proposition 11.22

import Mathlib
import Definitions.Def_Disjunctive_MonoidalStrengthening_Basic

namespace Disjunctive.MonoidalStrengthening

/-- Proposition 11.22 (Balas, *Disjunctive Programming*, Springer 2018, §11.9, p. 179-180).
Let `x ≥ 0` be integer on `J₁`, satisfy the background lower bounds `Σ_j a_ij x_j ≥ b_i`
(`i ∈ Q`), where — as in the book's setting — each bound is no larger than the corresponding
right-hand side, `b_i ≤ a_i0`, and satisfy the disjunction `∨_i (Σ_j a_ij x_j ≥ a_i0)`. Then for
any fixed `m^j ∈ M` (`j ∈ J₁`), `x` satisfies the strengthened disjunction (11.41)
`∨_i (Σ_{j∈J₁} (a_ij + (a_i0 - b_i) m^j_i) x_j + Σ_{j∉J₁} a_ij x_j ≥ a_i0)`.

Correction w.r.t. the retired version: the standing assumption `b_i ≤ a_i0` is now hypothesis
`hb`; without it a positive monoid entry multiplies the negative factor `a_i0 - b_i`. -/
theorem monoidal_strengthening_validity_v2 {q n : ℕ}
    (a : Fin q → Fin n → ℝ) (a0 b : Fin q → ℝ) (hb : ∀ i, b i ≤ a0 i) (J1 : Finset (Fin n))
    (m : Fin n → Fin q → ℤ) (hm_mem : ∀ j ∈ J1, (fun i => m j i) ∈ CutMonoid q)
    (x : Fin n → ℝ) (hx_nonneg : 0 ≤ x) (hx_int : ∀ j ∈ J1, ∃ k : ℤ, x j = (k : ℝ))
    (hx_lb : ∀ i, b i ≤ ∑ j, a i j * x j)
    (hx_disj : ∃ i, a0 i ≤ ∑ j, a i j * x j) :
    ∃ i, a0 i ≤ ∑ j ∈ J1, (a i j + (a0 i - b i) * (m j i : ℝ)) * x j +
      ∑ j ∈ Finset.univ \ J1, a i j * x j := by sorry

end Disjunctive.MonoidalStrengthening
