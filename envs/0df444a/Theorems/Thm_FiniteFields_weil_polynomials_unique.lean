-- Prove2me | Theorems.Thm_FiniteFields_weil_polynomials_unique
-- name    : FiniteFields.weil_polynomials_unique
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-21T08:38:51.548317+00:00
-- url     : https://prove2.me/theorems/0fb8adc3-1cf6-4b25-ae22-b3172e66869e
-- title:
--   Under the Riemann hypothesis, the polynomials $P_i$ of the Weil conjectures are determined by the zeta series
-- statement:
--   Let $q>1$ and $n\ge 0$ be integers and let $Z(T)\in\mathbb Q[[T]]$ be a formal power series. Say that a family $(P_i)_{i\ge 0}$ of polynomials $P_i\in\mathbb Z[T]$, together with finite multisets $\alpha_i$ of complex numbers, is a **weight decomposition** of $Z$ if:
--
--   1. $\displaystyle Z(T)\cdot\prod_{\substack{0\le i\le 2n\\ i\ \text{even}}}P_i(T)=\prod_{\substack{0\le i\le 2n\\ i\ \text{odd}}}P_i(T)$ in $\mathbb Q[[T]]$;
--   2. $P_0(T)=1-T$ and $P_{2n}(T)=1-q^nT$;
--   3. for $1\le i\le 2n-1$, $\displaystyle P_i(T)=\prod_{a\in\alpha_i}(1-aT)$ in $\mathbb C[T]$, and every $a\in\alpha_i$ is nonzero;
--   4. for $1\le i\le 2n-1$ and every $a\in\alpha_i$, $|a|=q^{i/2}$.
--
--   If $(P,\alpha)$ and $(P',\alpha')$ are two weight decompositions of the same series $Z$, then
--   $$P_i=P'_i\quad(0\le i\le 2n),\qquad \alpha_i=\alpha'_i\quad(1\le i\le 2n-1).$$
--
--   These are exactly the conclusions of the rationality and Riemann hypothesis parts of the Weil conjectures for a smooth projective variety of dimension $n$ over $\mathbb F_q$, with $Z$ its zeta function. The statement says that the polynomials $P_i$ (and their inverse roots) are intrinsic to the zeta function: the absolute values $q^{i/2}$ of the inverse roots separate the factors. Consequently the Betti number statement $\deg P_i=b_i$ of the Weil conjectures refers to well-defined polynomials.
--
--   **Formalization Note** Multisets $\alpha_i$ are Lean `Multiset ℂ`, and $P_i$ are mapped to $\mathbb Q[[T]]$ and $\mathbb C[T]$ through the canonical ring maps. The degree $2n-1$ uses truncated subtraction, so for $n=0$ the conditions 3 and 4 are empty.
-- source:
--   Auxiliary lemma (uniqueness of the factorization of the zeta function by weights), cf. A. Weil, *Numbers of solutions of equations in finite fields*, Bull. Amer. Math. Soc. 55 (1949), 497–508 (the conjectures are stated at the end of the paper); R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer 1977, Appendix C. Lean: original formalization for this project (Lean v4.33.1, Mathlib 0df444a), file `Bridge/WeightUniqueness.lean`.

import Mathlib

open Polynomial

theorem FiniteFields.weil_polynomials_unique (q n : ℕ) (hq : 1 < q) (Z : PowerSeries ℚ)
    (P P' : ℕ → ℤ[X]) (α α' : ℕ → Multiset ℂ)
    (h : Z * (∏ i ∈ (Finset.range (2 * n + 1)).filter Even,
            ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ)) =
        ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd,
            ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ) ∧
      P 0 = 1 - Polynomial.X ∧
      P (2 * n) = 1 - C ((q : ℤ) ^ n) * Polynomial.X ∧
      (∀ i, 1 ≤ i → i ≤ 2 * n - 1 →
        (P i).map (Int.castRingHom ℂ) = ((α i).map fun a => 1 - C a * Polynomial.X).prod ∧
        ∀ a ∈ α i, a ≠ 0) ∧
      (∀ i, 1 ≤ i → i ≤ 2 * n - 1 → ∀ a ∈ α i, ‖a‖ = (q : ℝ) ^ ((i : ℝ) / 2)))
    (h' : Z * (∏ i ∈ (Finset.range (2 * n + 1)).filter Even,
            ((P' i).map (Int.castRingHom ℚ) : PowerSeries ℚ)) =
        ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd,
            ((P' i).map (Int.castRingHom ℚ) : PowerSeries ℚ) ∧
      P' 0 = 1 - Polynomial.X ∧
      P' (2 * n) = 1 - C ((q : ℤ) ^ n) * Polynomial.X ∧
      (∀ i, 1 ≤ i → i ≤ 2 * n - 1 →
        (P' i).map (Int.castRingHom ℂ) = ((α' i).map fun a => 1 - C a * Polynomial.X).prod ∧
        ∀ a ∈ α' i, a ≠ 0) ∧
      (∀ i, 1 ≤ i → i ≤ 2 * n - 1 → ∀ a ∈ α' i, ‖a‖ = (q : ℝ) ^ ((i : ℝ) / 2))) :
    (∀ i ≤ 2 * n, P i = P' i) ∧ (∀ i, 1 ≤ i → i ≤ 2 * n - 1 → α i = α' i) := by sorry
