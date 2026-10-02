-- Prove2me | Theorems.Thm_Disjunctive_MonoidalStrengthening_monoidal_strengthening_disjunctive_cut
-- name    : Disjunctive.MonoidalStrengthening.monoidal_strengthening_disjunctive_cut
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:02:41.471731+00:00
-- url     : https://prove2.me/theorems/5d2a8aed-f928-4e75-9480-0d515aecc5ca
-- title:
--   Theorem 11.19 — the monoidally-strengthened disjunctive cut
-- statement:
--   This is Theorem 11.19 of Balas's *Disjunctive Programming*, cited to [24]: strengthening a
--   disjunctive cut using integrality on a subset $J_1$ of the variables produces a valid,
--   generally stronger cut.
--
--   Given a $q$-term disjunction $\bigvee_{h\in Q}(\sum_j a^h_j x_j \ge a^h_0)$ with a background
--   lower bound $\sum_j a^h_j x_j \ge b^h_0$ known for every term, every nonnegative $x$
--   satisfying both also satisfies
--   $$
--   \sum_{j\in J} \alpha_j x_j \ge \alpha_0, \qquad
--   \alpha_j = \begin{cases} \inf_{\mu^j\in M}\max_{h\in Q}\theta_h[a^h_j+\mu^j_h(a^h_0-b^h_0)], &
--   j\in J_1 \\ \max_{h\in Q}\theta_h a^h_j, & j\in J\setminus J_1\end{cases}, \qquad
--   \alpha_0 = \min_{h\in Q}\theta_h a^h_0.
--   $$
--
--   The book's proof (via the auxiliary Lemma 11.20) shows that for any fixed choice of $\mu^j\in
--   M$, replacing $a^h_j$ with $a^h_j+\mu^j_h(a^h_0-b^h_0)$ in the disjunction leaves it valid for
--   every feasible integer $x_j$ ($j\in J_1$): either the monoid-weighted sum vanishes on every
--   term (leaving the disjunction unchanged) or some term absorbs a nonnegative slack exactly
--   compensating for the shift. Taking the infimum over $M$ then gives the strongest such cut.
--
--   **Formalization Note.** `AlphaJStrengthened` uses `sInf` over the cut monoid `M` (a generally
--   infinite subset of `ℤ^q`), matching the book's own `inf_{μ^j∈M}` literally rather than fixing
--   one particular near-optimal `μ^j`.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 176, Theorem 11.19

import Mathlib
import Definitions.Def_Disjunctive_MonoidalStrengthening_Basic

namespace Disjunctive.MonoidalStrengthening

/-- Theorem 11.19 (Balas §11.8, p. 176, [24]): for the `q`-term disjunctive-cut situation with
per-term coefficients `a^h_j`, right-hand sides `a^h_0`, lower bounds `b^h_0 ≤ a^h_0` and
multipliers `θ_h ≥ 0`, every `x ≥ 0` satisfying `Σ_j a^h_j x_j ≥ b^h_0` for every `h` (the
background system (11.13)) and satisfying the disjunction `∨_h(Σ_j a^h_j x_j ≥ a^h_0)` also
satisfies the monoidally-strengthened cut `Σ_j α_j x_j ≥ α_0`, `α_j` given by `AlphaJStrengthened`
on `J₁` and `AlphaJUnstrengthened` elsewhere. The integrality of `x_j` for `j ∈ J₁` is (11.26)
and is what the monoid argument uses; without it the strengthened cut is invalid (`q = 2`,
`n = 1`, `J₁ = {0}`, `a¹ = 1.5`, `a¹₀ = 0.5`, `b¹ = -0.5`, `a² = -1.5`, `a²₀ = 0.5`,
`b² = -0.5`, `θ = (1,1)` gives the cut `x ≥ 1`, satisfied by no `x = 1/3` though `x = 1/3` meets
every other hypothesis). -/
theorem monoidal_strengthening_disjunctive_cut {q n : ℕ} [Nonempty (Fin q)]
    (acoef : Fin q → Fin n → ℝ) (a0 b0 theta : Fin q → ℝ) (J1 : Finset (Fin n))
    (hb0 : ∀ h, b0 h ≤ a0 h) (htheta : ∀ h, 0 ≤ theta h)
    (x : Fin n → ℝ) (hx_nonneg : 0 ≤ x)
    (hx_int : ∀ j ∈ J1, ∃ m : ℤ, x j = (m : ℝ))
    (hx_lb : ∀ h, b0 h ≤ ∑ j, acoef h j * x j)
    (hx_disj : ∃ h, a0 h ≤ ∑ j, acoef h j * x j) :
    Alpha0 theta a0 ≤
      ∑ j ∈ J1, AlphaJStrengthened theta a0 b0 acoef j * x j +
        ∑ j ∈ Finset.univ \ J1, AlphaJUnstrengthened theta acoef j * x j := by sorry

end Disjunctive.MonoidalStrengthening
