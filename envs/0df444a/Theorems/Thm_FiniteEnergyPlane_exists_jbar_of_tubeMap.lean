-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_jbar_of_tubeMap
-- name    : FiniteEnergyPlane.exists_jbar_of_tubeMap
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-16T18:06:36.57408+00:00
-- url     : https://prove2.me/theorems/ba063d19-4561-4493-92bd-d4433ba0c062
-- title:
--   The pulled-back almost complex structure on a tube around a holomorphic plane
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be a strictly star-shaped level with a compatible complex structure $J$ on $\xi$, and let $\tilde J$ be the induced almost complex structure on $\mathbb{R}^4 \setminus \{0\}$. Let $u : \mathbb{C} \to \mathbb{R}^4$ be smooth and $\tilde J$-holomorphic, and let $N(z) : \mathbb{C} \to \mathbb{R}^4$ be real linear maps depending smoothly on $z$ with $N(z)(i\nu) = \tilde J(u(z))\, N(z)\nu$. Put $\Phi(z, w) = u(z) + N(z) w$.
--
--   If $\rho > 0$ and, for all $(z, w) \in \mathbb{C} \times B_\rho(0)$, $\Phi(z, w) \neq 0$ and $D\Phi(z, w)$ is injective, then there is a smooth family $\bar J(z, w)$ of real linear maps of $\mathbb{C} \times \mathbb{C}$ on $\mathbb{C} \times B_\rho(0)$ with $\bar J^2 = -1$, $\bar J(z, 0) = i \oplus i$ for all $z$, and $D\Phi \circ \bar J = \tilde J(\Phi) \circ D\Phi$ on $\mathbb{C} \times B_\rho(0)$.
--
--   Role: this is the almost complex structure part of a standard tube structure around a holomorphic plane.
--
--   Formalization note: $\mathbb{R}^4$ is `V 1`, $\tilde J$ is `Jtilde H J`, $i \oplus i$ is `jStd`, and $\tilde J$-holomorphy is `JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ u`.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The pulled-back structure on a tube. Let `u : ℂ → V 1` be smooth and `J̃`-holomorphic, let
`N z : ℂ →L[ℝ] V 1` be smooth and complex linear for `J̃(u z)`, and put `Φ(z, w) = u z + N z w`.
If on `ℂ × ball 0 ρ` the point `Φ` is nonzero and `DΦ` is injective, then there is a smooth
family `Jbar` on `ℂ × ball 0 ρ` with `Jbar² = -1`, `Jbar(z, 0) = i ⊕ i` and
`DΦ ∘ Jbar = J̃(Φ) ∘ DΦ`. -/
theorem exists_jbar_of_tubeMap (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ u)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (hNJ : ∀ (z ν : ℂ), N z (Complex.I * ν) = Jtilde H J (u z) (N z ν))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hΦ : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0 ∧
      Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p)) :
    ∃ Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ,
      ContDiffOn ℝ ∞ Jbar (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
      (∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
        (Jbar p).comp (Jbar p) = -ContinuousLinearMap.id ℝ (ℂ × ℂ)) ∧
      (∀ z : ℂ, Jbar (z, 0) = jStd) ∧
      ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
        (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p).comp (Jbar p) =
          (Jtilde H J (u p.1 + N p.1 p.2)).comp
            (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p) := by
  sorry

end FiniteEnergyPlane
