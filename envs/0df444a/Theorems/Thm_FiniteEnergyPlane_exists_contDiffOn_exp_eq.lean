-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_contDiffOn_exp_eq
-- name    : FiniteEnergyPlane.exists_contDiffOn_exp_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T11:38:13.145482+00:00
-- url     : https://prove2.me/theorems/348682f5-aa07-4ff7-8666-e83c09d66082
-- title:
--   A smooth angle function for a smooth map from an interval to the unit circle
-- statement:
--   Let $S\subset\mathbb{R}$ be open and convex (an open interval, possibly empty or unbounded), $l\ge 1$, and let $\rho:\mathbb{R}\to\mathbb{C}$ be $C^l$ on $S$ with $|\rho(t)|=1$ for all $t\in S$. Then there is $\theta:\mathbb{R}\to\mathbb{R}$, $C^l$ on $S$, with
--   $$\rho(t)=e^{2\pi i\,\theta(t)}\qquad (t\in S).$$
--
--   Role: a $C^l$ map from an interval to the unit circle admits a $C^l$ lift through the covering $\theta\mapsto e^{2\pi i\theta}$. This produces smooth angle (gauge) functions, for example for a smooth family of rotations $z\mapsto e^{2\pi i\theta(t)}z$ of the domain of a family of maps.
--
--   **Formalization Note** "$C^l$ on $S$" is `ContDiffOn ℝ l`; the exponent is written `Complex.exp (((2 * π * θ t : ℝ) : ℂ) * Complex.I)`.
-- source:
--   General analysis lemma; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemma 7.4

import Mathlib

namespace FiniteEnergyPlane

open Filter Topology MeasureTheory
open scoped ContDiff Real

/-- A map `ρ : ℝ → ℂ` that is `C^l` (`l ≥ 1`) on an open convex set `S ⊆ ℝ` and takes values in
the unit circle has a `C^l` angle function: there is `θ`, `C^l` on `S`, with
`ρ t = exp (2π i θ t)` for every `t ∈ S`. -/
theorem exists_contDiffOn_exp_eq {l : ℕ} (hl : 1 ≤ l) {S : Set ℝ} (hS : IsOpen S)
    (hSc : Convex ℝ S) {ρ : ℝ → ℂ} (hρ : ContDiffOn ℝ l ρ S) (hρ1 : ∀ t ∈ S, ‖ρ t‖ = 1) :
    ∃ θ : ℝ → ℝ, ContDiffOn ℝ l θ S ∧
      ∀ t ∈ S, Complex.exp (((2 * π * θ t : ℝ) : ℂ) * Complex.I) = ρ t := by
  sorry

end FiniteEnergyPlane
