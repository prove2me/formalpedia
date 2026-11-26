-- Prove2me | Theorems.Thm_FiniteEnergyPlane_laplacian_aCoord_eq_dlambdaDensity
-- name    : FiniteEnergyPlane.laplacian_aCoord_eq_dlambdaDensity
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-26T17:30:58.544254+00:00
-- url     : https://prove2.me/theorems/a2c6e172-1c34-4038-b298-d6f941b5ada7
-- title:
--   The R-coordinate of a pseudoholomorphic map into a symplectization is subharmonic
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^{2n+2}$ be strictly star-shaped, $J$ a compatible complex structure on $\xi$, and $\tilde J$ the induced almost complex structure on the symplectization $\mathbb{R} \times S \cong \mathbb{R}^{2n+2} \setminus \{0\}$. Let $U \subseteq \mathbb{C}$ be open and $u : \mathbb{C} \to \mathbb{R}^{2n+2}$ smooth on $U$, nonvanishing and $\tilde J$-holomorphic there, and write $u = (a, w)$ with $a = \mathrm{aCoord} \circ u$ and $w = \mathrm{proj} \circ u$. Then $a$ is smooth on $U$ and
--   $$\Delta a = \omega_0(\partial_s w, \partial_t w) \quad \text{on } U,$$
--   the integrand of the $d\lambda$-energy. In particular $a$ is subharmonic on $U$.
--
--   Role: the identity that makes the maximum principle and the boundary point lemma available for the $\mathbb{R}$-coordinate of pseudoholomorphic curves in the symplectization.
--
--   Formalization Note: $\Delta$ is Mathlib's Laplacian on $\mathbb{C}$; the right-hand side is `dlambdaDensity H u z`.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515-563, Section 2.2; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II, GAFA 5 (1995), Section 2

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib.Analysis.InnerProductSpace.Laplacian

namespace FiniteEnergyPlane

open Laplacian
open scoped ContDiff

/-- Let `u` be a smooth `J̃`-holomorphic map from an open set `U ⊆ ℂ` to the symplectization
`ℝ × S = ℝ^{2n+2} \ {0}`, and write `u = (a, w)`. Then `a = aCoord ∘ u` is smooth on `U` and its
Laplacian is the `dλ`-density of `u`: `Δa = ω₀(∂ₛw, ∂ₜw)` on `U`. In particular `a` is subharmonic. -/
theorem laplacian_aCoord_eq_dlambdaDensity {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U) (u : ℂ → V n)
    (hu : ContDiffOn ℝ ∞ u U) (hu0 : ∀ z ∈ U, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) U u) :
    ContDiffOn ℝ ∞ (fun z => aCoord H (u z)) U ∧
      ∀ z ∈ U, Δ (fun z => aCoord H (u z)) z = dlambdaDensity H u z := by
  sorry

end FiniteEnergyPlane
