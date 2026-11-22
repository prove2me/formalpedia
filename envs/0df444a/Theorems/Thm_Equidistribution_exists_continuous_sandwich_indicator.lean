-- Prove2me | Theorems.Thm_Equidistribution_exists_continuous_sandwich_indicator
-- name    : Equidistribution.exists_continuous_sandwich_indicator
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:31:32.421657+00:00
-- url     : https://prove2.me/theorems/8cc8566d-c409-43c3-b216-0da56e776f8b
-- title:
--   Lemma B.5.2.2 — the indicator of an open set with $\mu$-null boundary lies between two continuous functions whose integrals differ by less than $\varepsilon$
-- statement:
--   **Lemma B.5.2.2 (continuous approximation of the indicator of a set with null boundary).** Let $X$ be a compact Hausdorff space, $\mu$ a regular Borel measure on $X$, and $U\subset X$ an open subset whose boundary is $\mu$-null, $\mu(\partial U)=0$. Then for every $\varepsilon>0$ there exist continuous functions $u_1,u_2\colon X\to[0,1]$ such that
--   $$u_1(x)\le \mathbf 1_U(x)\le u_2(x)\qquad\text{for all }x\in X,$$
--   and
--   $$\int_X\bigl(u_2-u_1\bigr)(x)\,d\mu(x)<\varepsilon .$$
--
--   Here $\mathbf 1_U$ is the indicator function of $U$. The lemma is the device by which an equidistribution statement for continuous test functions (weak convergence of measures) is transferred to indicator functions of sets with null boundary, and from there to Riemann-integrable functions; the source uses it in this way in the proof of the Kronecker–Weyl theorem (Theorem B.5.2.1(2), eqs. (B.5.2.4)–(B.5.2.8)). Its proof in the source combines the regularity of $\mu$ with Urysohn's lemma.
--
--   **Formalization Note.** "Regular Borel measure" is Mathlib's `MeasureTheory.Measure.Regular` on a space with its Borel σ-algebra (`BorelSpace X`): finite on compact sets, outer regular, and inner regular on open sets with respect to compact sets; since $X$ is compact, $\mu$ is finite, as the source's proof uses. The functions are bundled continuous maps `C(X, ℝ)`; the conditions `0 ≤ u₁ x` and `u₂ x ≤ 1` express that they take values in $[0,1]$ (the other two bounds follow from the inequalities with the indicator `U.indicator (fun _ => 1)`), and $\partial U$ is `frontier U`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 627–628, Lemma B.5.2.2, eqs. (B.5.2.2)–(B.5.2.3)

import Mathlib

open MeasureTheory

set_option autoImplicit false

namespace Equidistribution

theorem exists_continuous_sandwich_indicator {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.Regular]
    (U : Set X) (hU : IsOpen U) (h0 : μ (frontier U) = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ u₁ u₂ : C(X, ℝ),
      (∀ x, 0 ≤ u₁ x ∧ u₁ x ≤ U.indicator (fun _ => (1 : ℝ)) x ∧
        U.indicator (fun _ => (1 : ℝ)) x ≤ u₂ x ∧ u₂ x ≤ 1) ∧
      ∫ x, (u₂ x - u₁ x) ∂μ < ε := by sorry

end Equidistribution
