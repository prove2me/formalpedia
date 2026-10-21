-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_extension_of_energy_lt_top
-- name    : FiniteEnergyPlane.exists_extension_of_energy_lt_top
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-20T23:24:26.339358+00:00
-- url     : https://prove2.me/theorems/3f470c34-204d-454a-bef8-d8c61f6084d2
-- title:
--   Removal of singularities for pseudoholomorphic maps of finite energy
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $J$ a smooth almost complex structure on an open set $O\subseteq E$, and $K\subseteq O$ compact. Let $D\subset\mathbb{C}$ be the open unit disc and $u$ a $C^\infty$ $J$-holomorphic map on $D\setminus\{0\}$ with $u(D\setminus\{0\})\subseteq K$ and
--   $$\int_{D\setminus\{0\}}\|Du(z)\|^2\,dz<\infty.$$
--   Then there is a $C^\infty$ $J$-holomorphic map $v$ on $D$ with $v(D)\subseteq K$ and $v=u$ on $D\setminus\{0\}$.
--
--   **Formalization Note** The energy is a lower integral in `ℝ≥0∞` of the squared operator norm. Wendl and Zinger assume a compact target manifold (or a compact image); here the image lies in a compact subset $K$ of the domain $O$ of $J$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Theorem 9.2, p. 152; A. Zinger, Notes on J-holomorphic maps, arXiv:1706.00331, Proposition 5.1

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Removal of singularities: Zinger, *Notes on J-holomorphic maps*, Proposition 5.1; Wendl,
Theorem 9.2 (p. 152). Let `J` be a smooth almost complex structure on an open set `O ⊆ E` and
`K ⊆ O` compact. A smooth `J`-holomorphic map on the punctured unit disc with values in `K` and
finite Dirichlet energy `∫ ‖Du‖²` extends to a smooth `J`-holomorphic map on the disc with values
in `K`. (Zinger assumes the target manifold compact; here the image lies in a compact `K ⊆ O`.) -/
theorem exists_extension_of_energy_lt_top {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (K : Set E) (hK : IsCompact K) (hKO : K ⊆ O)
    (u : ℂ → E) (hu : ContDiffOn ℝ ∞ u (ball 0 1 \ {0}))
    (hhol : JHolomorphic.IsJHolomorphicOn J (ball 0 1 \ {0}) u)
    (hmaps : Set.MapsTo u (ball 0 1 \ {0}) K)
    (hE : ∫⁻ z in ball 0 1 \ {0}, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) < ⊤) :
    ∃ v : ℂ → E, ContDiffOn ℝ ∞ v (ball 0 1) ∧ JHolomorphic.IsJHolomorphicOn J (ball 0 1) v ∧
      Set.MapsTo v (ball 0 1) K ∧ ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → v z = u z := by
  sorry

end FiniteEnergyPlane
