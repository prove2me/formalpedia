-- Prove2me | Theorems.Thm_FiniteEnergyPlane_eq_trivialCylinder_of_dlambdaEnergy_eq_zero
-- name    : FiniteEnergyPlane.eq_trivialCylinder_of_dlambdaEnergy_eq_zero
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-20T23:25:13.001693+00:00
-- url     : https://prove2.me/theorems/8153bc0a-7230-41c8-98ff-e3de94f5499f
-- title:
--   Finite-energy cylinders with vanishing $d\lambda$-energy are trivial cylinders
-- statement:
--   Let $S=H^{-1}(1)$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $u$ a nonconstant finite-energy $\tilde J$-holomorphic curve on $\mathbb{C}\setminus\{0\}$ with $\int_{\mathbb{C}\setminus\{0\}}u^*d\lambda_0=0$. Then there are a periodic Reeb orbit $P$, an integer $k\neq0$ and $c\in\mathbb{C}\setminus\{0\}$ with
--   $$u(z)=F_P(c\,z^k)\qquad\text{for all }z\neq0.$$
--
--   **Formalization Note** The cylinder $\mathbb{R}\times S^1$ is $\mathbb{C}\setminus\{0\}$, $(s,t)\mapsto e^{2\pi(s+it)}$; Wendl's "biholomorphically equivalent to a trivial cylinder over a closed Reeb orbit" is the explicit form $F_P(cz^k)$, with $F_P$ as in the setting and $z^k$ an integer power. Wendl's lemma also covers the plane and general stable Hamiltonian structures; this item is the cylinder case in the symplectization of a star-shaped level.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lemma 9.9, p. 158 (case of the cylinder)

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Wendl, Lemma 9.9 (p. 158), cylinder case. A nonconstant finite-energy `J̃`-holomorphic
cylinder `u : ℂ \ {0} → V n \ {0}` with vanishing `dλ`-energy is a trivial cylinder: there are a
periodic Reeb orbit `P`, an integer `k ≠ 0` and `c ≠ 0` with `u(z) = F_P(c zᵏ)`. (The cylinder
`ℝ × S¹` is `ℂ \ {0}` by `e^{2π(s+it)}`; `F_P(w) = |w|^{T/π} x(T arg w / 2π)` in the coordinate
`y = e^{2a} x`.) -/
theorem eq_trivialCylinder_of_dlambdaEnergy_eq_zero {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J {z | z ≠ 0} u)
    (hnc : ∃ z₁ : ℂ, z₁ ≠ 0 ∧ ∃ z₂ : ℂ, z₂ ≠ 0 ∧ u z₁ ≠ u z₂)
    (hzero : dlambdaEnergy H {z | z ≠ 0} u = 0) :
    ∃ P : ReebOrbit H, ∃ k : ℤ, k ≠ 0 ∧ ∃ c : ℂ, c ≠ 0 ∧
      ∀ z : ℂ, z ≠ 0 → u z = trivialCylinder P (c * z ^ k) := by
  sorry

end FiniteEnergyPlane
