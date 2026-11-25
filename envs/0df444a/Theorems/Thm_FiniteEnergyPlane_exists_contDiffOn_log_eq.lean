-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_contDiffOn_log_eq
-- name    : FiniteEnergyPlane.exists_contDiffOn_log_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-25T13:31:53.057832+00:00
-- url     : https://prove2.me/theorems/8592e869-8195-56df-b75f-bc977e51423c
-- title:
--   Local $C^l$ logarithm of a nonvanishing curve in $\mathbb{C}$
-- statement:
--   Let $\eta>0$ and let $A:\mathbb{R}\to\mathbb{C}$ be $C^l$ on $(-\eta,\eta)$ with $A(0)\ne0$. Then there are $0<\rho\le\eta$ and a map $f:\mathbb{R}\to\mathbb{C}$, $C^l$ on $(-\rho,\rho)$, with $e^{f(s)}=A(s)$ for $|s|<\rho$.
--
--   Elementary reusable fact on curves in $\mathbb{C}\setminus\{0\}$.
--
--   **Formalization Note** Intervals are balls of $\mathbb{R}$, and $C^l$ is real differentiability of natural order $l$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7.2.2

import Mathlib

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff Real

/-- A `C^l` map `A : ℝ → ℂ` near `0` with `A 0 ≠ 0` has, on a smaller interval around `0`, a `C^l`
logarithm: `exp (f s) = A s`. -/
theorem exists_contDiffOn_log_eq {l : ℕ} {η : ℝ} (hη : 0 < η) {A : ℝ → ℂ} (hA : ContDiffOn ℝ l A (ball 0 η))
    (hA0 : A 0 ≠ 0) : ∃ ρ > 0, ρ ≤ η ∧ ∃ f : ℝ → ℂ, ContDiffOn ℝ l f (ball 0 ρ) ∧
      ∀ s ∈ ball (0 : ℝ) ρ, Complex.exp (f s) = A s := by
  sorry

end FiniteEnergyPlane
