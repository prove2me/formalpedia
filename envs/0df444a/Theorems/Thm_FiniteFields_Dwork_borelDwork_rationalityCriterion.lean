-- Prove2me | Theorems.Thm_FiniteFields_Dwork_borelDwork_rationalityCriterion
-- name    : FiniteFields.Dwork.borelDwork_rationalityCriterion
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T01:59:50.303401+00:00
-- url     : https://prove2.me/theorems/a7d181b9-e61b-4e45-a83e-1637ca3c996e
-- title:
--   Borel–Dwork rationality criterion (Dwork's Theorem 2, $p$-adically meromorphic case)
-- statement:
--   **Setting.** Let $p$ be a prime and let $K$ be a field of characteristic $0$, complete for a nontrivial nonarchimedean (ultrametric) absolute value $|\cdot|_K$, normalized so that
--   $$p^{-1} \le |p|_K < 1 .$$
--   A power series $G = \sum_m g_m X^m \in K[[X]]$ is called **entire** if $|g_m|_K\, R^m \to 0$ as $m \to \infty$ for every real $R \ge 0$. A series $F \in K[[X]]$ is called **$p$-adically meromorphic** if there are entire series $G, H \in K[[X]]$ with $H(0) = 1$ and $H \cdot F = G$.
--
--   **Statement.** Let $F = \sum_{m \ge 0} a_m X^m \in \mathbb{Q}[[X]]$ and assume:
--
--   1. (integrality) $a_m \in \mathbb{Z}$ for every $m \ge 0$;
--   2. (Archimedean growth) there are rational numbers $C$ and $B \ge 1$ such that $|a_m| \le C\, B^m$ for every $m \ge 0$;
--   3. ($p$-adic meromorphy) the image of $F$ in $K[[X]]$ is $p$-adically meromorphic.
--
--   Then $F$ is rational: there exist polynomials $P, Q \in \mathbb{Q}[X]$ with $Q \ne 0$, $Q(0) \ne 0$ and
--   $$Q(X)\, F(X) = P(X) \qquad \text{in } \mathbb{Q}[[X]].$$
--
--   This is the rationality criterion of Dwork's §4 (Theorem 2), in the case where $F$ is meromorphic on the whole $p$-adic plane: condition 2 says that $F$ converges in the complex disc of radius $1/B$, and the condition $Rr > 1$ of Theorem 2 holds automatically since $r = \infty$. Applied to zeta functions, it turns $p$-adic meromorphy into rationality over $\mathbb{Q}$.
--
--   **Formalization Note.** Integrality is expressed by an auxiliary sequence $z : \mathbb{N} \to \mathbb{Z}$ with $a_m = z_m$. The constant $C$ is not assumed positive. The field $K$ replaces Dwork's $\Omega$ (the completion of an algebraic closure of $\mathbb{Q}_p$); the hypothesis $p^{-1} \le |p|_K < 1$ relates its absolute value to the standard $p$-adic one. Rationality is `IsRationalPowerSeries`, and meromorphy is the global predicate `IsPadicMeromorphic` described above.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648, §4, Theorem 2, (28)–(31), building on the result of Borel and the Hankel-determinant criterion (27); stated here in the special case where the series is meromorphic on the whole $p$-adic plane ($r = \infty$). Lean: ported from the `finite_fields` project (commit e8b5bf14), file `WeilConjectures/Dwork/BorelDworkCriterion/Criterion.lean`, declaration `WeilConjectures.Dwork.borelDwork_rationalityCriterion`

import Mathlib
import Definitions.Def_FiniteFields_Dwork_Meromorphy

open PowerSeries Finset
open scoped Polynomial
open FiniteFields.Dwork
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable [CharZero K]

theorem FiniteFields.Dwork.borelDwork_rationalityCriterion {p : ℕ} (hp : p.Prime)
    (hpnorm : ((p : ℝ))⁻¹ ≤ ‖(p : K)‖) (hplt : ‖(p : K)‖ < 1)
    (F : ℚ⟦X⟧) (z : ℕ → ℤ) (hz : ∀ m, PowerSeries.coeff m F = (z m : ℚ))
    {C B : ℚ} (hB : 1 ≤ B) (hgrowth : ∀ m : ℕ, |PowerSeries.coeff m F| ≤ C * B ^ m)
    (hmero : IsPadicMeromorphic (PowerSeries.map (algebraMap ℚ K) F)) :
    IsRationalPowerSeries F := by sorry
