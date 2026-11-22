-- Prove2me | Theorems.Thm_FiniteEnergyPlane_contDiffOn_of_apply_eq_of_injective_fderiv
-- name    : FiniteEnergyPlane.contDiffOn_of_apply_eq_of_injective_fderiv
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T11:37:56.206179+00:00
-- url     : https://prove2.me/theorems/cf7c1ebf-2cab-4077-9c29-6a9595e5d9f3
-- title:
--   Regularity of a solution curve of a parametrized equation with injective partial derivative
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $S\subset\mathbb{R}$ open and $l\ge 1$. Let $F:\mathbb{R}\times\mathbb{C}\to E$ be $C^l$ on $S\times\mathbb{C}$ and $g:\mathbb{R}\to E$ be $C^l$ on $S$. Let $\rho:\mathbb{R}\to\mathbb{C}$ be continuous on $S$ with
--   $$F(t,\rho(t))=g(t)\qquad (t\in S),$$
--   and suppose that for every $t\in S$ the real derivative of $w\mapsto F(t,w)$ at $w=\rho(t)$ is injective. Then $\rho$ is $C^l$ on $S$.
--
--   Role: a continuous curve of solutions $w=\rho(t)$ of a parametrized equation $F(t,w)=g(t)$, along which the partial derivative in $w$ is injective (but $E$ may have larger dimension than $\mathbb{C}$), inherits the regularity of the data. A typical use is a curve of preimages $\rho(t)$ of points $g(t)$ under a smooth family of immersions $F(t,\cdot)$.
--
--   **Formalization Note** "$C^l$ on a set" is `ContDiffOn ℝ l`; the derivative of $w\mapsto F(t,w)$ is `fderiv ℝ (fun w => F (t, w)) (ρ t)` as a real-linear map $\mathbb{C}\to E$.
-- source:
--   General analysis lemma; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemma 7.4

import Mathlib

namespace FiniteEnergyPlane

open Filter Topology
open scoped ContDiff

/-- Let `F : ℝ × ℂ → E` (with `E` finite-dimensional) and `g : ℝ → E` be `C^l` (`l ≥ 1`) on
`S × ℂ` and `S`, for an open set `S ⊆ ℝ`. If `ρ : ℝ → ℂ` is continuous on `S`, satisfies
`F (t, ρ t) = g t` on `S`, and the derivative of `w ↦ F (t, w)` at `ρ t` is injective for every
`t ∈ S`, then `ρ` is `C^l` on `S`. -/
theorem contDiffOn_of_apply_eq_of_injective_fderiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {l : ℕ} (hl : 1 ≤ l) {S : Set ℝ} (hS : IsOpen S)
    {F : ℝ × ℂ → E} {g : ℝ → E} {ρ : ℝ → ℂ}
    (hF : ContDiffOn ℝ l F (S ×ˢ Set.univ)) (hg : ContDiffOn ℝ l g S) (hρ : ContinuousOn ρ S)
    (heq : ∀ t ∈ S, F (t, ρ t) = g t)
    (hinj : ∀ t ∈ S, Function.Injective (fderiv ℝ (fun w => F (t, w)) (ρ t))) :
    ContDiffOn ℝ l ρ S := by
  sorry

end FiniteEnergyPlane
