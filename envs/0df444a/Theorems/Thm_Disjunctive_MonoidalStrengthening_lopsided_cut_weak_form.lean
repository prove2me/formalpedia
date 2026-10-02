-- Prove2me | Theorems.Thm_Disjunctive_MonoidalStrengthening_lopsided_cut_weak_form
-- name    : Disjunctive.MonoidalStrengthening.lopsided_cut_weak_form
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T17:03:52.689376+00:00
-- url     : https://prove2.me/theorems/eb593b32-8f6c-40ca-81d8-a6aaddd3416e
-- title:
--   Corollary 11.25 — a weak Lopsided cut, no monoid optimization
-- statement:
--   This is Corollary 11.25 of Balas's *Disjunctive Programming*: a simplified, weaker cousin of
--   Theorem 11.23's Lopsided cut that needs no monoid optimization, and the immediate precursor
--   (in the same subsection) to the goal theorem's GMI-cut refinement.
--
--   For each disjunct index $k \in Q$, the cut $\delta^k x \ge 1$ is valid, with
--   $$
--   \delta^k_j := \begin{cases}
--   \min\Big\{\dfrac{a_{kj}+a_{k0}-b_k}{a_{k0}},\ \beta_j\Big\}, & j \in J_1 \\[4pt]
--   \beta_j, & j \in J \setminus J_1
--   \end{cases}
--   $$
--   where $\beta_j = \max_{i\in Q} a_{ij}/a_{i0}$ is the unstrengthened, normalized cut
--   coefficient of (11.38)/(11.39).
--
--   **Formalization Note.** Unlike Theorem 11.23's Lopsided cut $\bar\beta^k_j$ (which minimizes
--   over the monoid $M$ subject to $m^k_j\ge 0$, not drafted this pass), $\delta^k_j$ needs no
--   monoid optimization at all: it simply takes the smaller of the unstrengthened coefficient and
--   a single closed-form quantity depending only on term $k$, matching the corollary's own
--   framing as "a weaker version of the lopsided cuts that does not require optimizing over a
--   monoid."
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 183, Corollary 11.25

import Mathlib
import Definitions.Def_Disjunctive_MonoidalStrengthening_Basic

namespace Disjunctive.MonoidalStrengthening

/-- Corollary 11.25 (Balas §11.9, p. 183): for each `k ∈ Q`, the cut `δ^k x ≥ 1` is valid, with
`δ^k_j := min{(a_kj+a_k0-b_k)/a_k0, β_j}` for `j ∈ J₁` (`β_j` the unstrengthened coefficient) and
`δ^k_j := β_j` for `j ∈ J\J₁` — a weaker version of the Lopsided cut of Theorem 11.23 that does
not require optimizing over the monoid. The disjunction (11.38) has `a_{i0} > 0`, which the normalized coefficients divide by; with
`a_{i0} = 0`, `b_i ≤ 0` and `x = 0` the conclusion reads `1 ≤ 0`. -/
theorem lopsided_cut_weak_form {q n : ℕ} [Nonempty (Fin q)]
    (a : Fin q → Fin n → ℝ) (a0 b : Fin q → ℝ) (J1 : Finset (Fin n)) (k : Fin q)
    (ha0 : ∀ i, 0 < a0 i)
    (x : Fin n → ℝ) (hx_nonneg : 0 ≤ x) (hx_int : ∀ j ∈ J1, ∃ m : ℤ, x j = (m : ℝ))
    (hx_lb : ∀ i, b i ≤ ∑ j, a i j * x j)
    (hx_disj : ∃ i, a0 i ≤ ∑ j, a i j * x j) :
    1 ≤ ∑ j ∈ J1, min ((a k j + a0 k - b k) / a0 k) (BetaJUnstrengthened a a0 j) * x j +
      ∑ j ∈ Finset.univ \ J1, BetaJUnstrengthened a a0 j * x j := by sorry

end Disjunctive.MonoidalStrengthening
