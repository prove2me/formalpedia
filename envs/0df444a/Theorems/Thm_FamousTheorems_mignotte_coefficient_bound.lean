-- Prove2me | Theorems.Thm_FamousTheorems_mignotte_coefficient_bound
-- name    : FamousTheorems.mignotte_coefficient_bound
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:08:53.341753+00:00
-- url     : https://prove2.me/theorems/e27650d6-cbc8-4afa-9cfa-e832817ee71c
-- title:
--   Mignotte's coefficient bound
-- statement:
--   **Mignotte's coefficient bound.** Let $g,h$ be complex polynomials with Mahler measure $M(h)\ge1$. Then every coefficient of $g$ satisfies
--   $$|g_n|\le\binom{\deg g}{n}\,M(gh).$$
--
--   In the typical application $g$ divides an integer polynomial $f=gh$, and $h$ is a nonzero integer polynomial, so $M(h)\ge1$. The bound then limits the coefficients of any factor $g$ of $f$ in terms of $f$ alone, using $M(f)\le\|f\|_2$ (Landau's inequality). This is the basis of the Berlekamp–Zassenhaus and LLL algorithms for factoring integer polynomials.
--
--   **Formalization note.** Mathlib's `Polynomial.norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure`. `g.natDegree.choose n` is the binomial coefficient $\binom{\deg g}{n}$, cast to $\mathbb R$, and `mahlerMeasure` is the Mahler measure.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Polynomial.norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem mignotte_coefficient_bound (n : ℕ) (g h : Polynomial ℂ) (hh : 1 ≤ h.mahlerMeasure) :
    ‖g.coeff n‖ ≤ (g.natDegree.choose n : ℝ) * (g * h).mahlerMeasure := by sorry

end FamousTheorems
