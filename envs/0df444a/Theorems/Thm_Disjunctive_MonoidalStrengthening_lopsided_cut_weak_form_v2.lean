-- Prove2me | Theorems.Thm_Disjunctive_MonoidalStrengthening_lopsided_cut_weak_form_v2
-- name    : Disjunctive.MonoidalStrengthening.lopsided_cut_weak_form_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:56.796868+00:00
-- url     : https://prove2.me/theorems/5cb02b49-eabb-4541-bb36-d0239e75441b
-- title:
--   Corollary 11.25 — a weak Lopsided cut needing no monoid optimization (with $b_i \le a_{i0}$)
-- statement:
--   This is Corollary 11.25 of Balas's *Disjunctive Programming*: a weaker version of the Lopsided cut of Theorem 11.23 that requires no optimization over the cut monoid.
--
--   Consider the normalized disjunction $\bigvee_{i\in Q}\big(\sum_j a_{ij}x_j \ge a_{i0}\big)$ with $a_{i0} > 0$, background lower bounds $\sum_j a_{ij}x_j \ge b_i$ with $b_i \le a_{i0}$ ($i\in Q$), and let $\beta_j := \max_{i\in Q} a_{ij}/a_{i0}$. For every $k\in Q$ define
--   $$
--   \delta^k_j := \begin{cases}\min\Big\{\dfrac{a_{kj}+a_{k0}-b_k}{a_{k0}},\ \beta_j\Big\}, & j\in J_1,\\[4pt] \beta_j, & j\in J\setminus J_1.\end{cases}
--   $$
--   Then every $x\ge 0$ with $x_j\in\mathbb Z$ for $j\in J_1$ that satisfies the background bounds and the disjunction satisfies $\delta^k x \ge 1$.
--
--   **Formalization Note.** The retired version omitted the standing assumption $b_i \le a_{i0}$, so $(a_{kj}+a_{k0}-b_k)/a_{k0}$ could be negative and the cut invalid ($q=n=1$, $a=a_0=1$, $b=3$, $x=3$). The new statement adds $b_i\le a_{i0}$ for all $i$ (hypothesis `hb`), as in the section's setting; everything else is unchanged ($a_{i0}>0$ is kept, $Q$ is nonempty because $\beta_j$ is a maximum over $Q$).
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §11.9, p. 183, Corollary 11.25

import Mathlib
import Definitions.Def_Disjunctive_MonoidalStrengthening_Basic

namespace Disjunctive.MonoidalStrengthening

/-- Corollary 11.25 (Balas, *Disjunctive Programming*, Springer 2018, §11.9, p. 183). For the
normalized disjunction (11.38) `∨_i (Σ_j a_ij x_j ≥ a_i0)` with `a_i0 > 0` and background lower
bounds `Σ_j a_ij x_j ≥ b_i` satisfying the standing assumption `b_i ≤ a_i0`, for each `k ∈ Q` the
cut `δ^k x ≥ 1` is valid for every `x ≥ 0`, integer on `J₁`, satisfying the bounds and the
disjunction, where `δ^k_j := min{(a_kj + a_k0 - b_k)/a_k0, β_j}` for `j ∈ J₁` and `δ^k_j := β_j`
otherwise (`β_j = max_i a_ij/a_i0`).

Correction w.r.t. the retired version: the standing assumption `b_i ≤ a_i0` is now hypothesis
`hb`. -/
theorem lopsided_cut_weak_form_v2 {q n : ℕ} [Nonempty (Fin q)]
    (a : Fin q → Fin n → ℝ) (a0 b : Fin q → ℝ) (J1 : Finset (Fin n)) (k : Fin q)
    (ha0 : ∀ i, 0 < a0 i) (hb : ∀ i, b i ≤ a0 i)
    (x : Fin n → ℝ) (hx_nonneg : 0 ≤ x) (hx_int : ∀ j ∈ J1, ∃ m : ℤ, x j = (m : ℝ))
    (hx_lb : ∀ i, b i ≤ ∑ j, a i j * x j)
    (hx_disj : ∃ i, a0 i ≤ ∑ j, a i j * x j) :
    1 ≤ ∑ j ∈ J1, min ((a k j + a0 k - b k) / a0 k) (BetaJUnstrengthened a a0 j) * x j +
      ∑ j ∈ Finset.univ \ J1, BetaJUnstrengthened a a0 j * x j := by sorry

end Disjunctive.MonoidalStrengthening
