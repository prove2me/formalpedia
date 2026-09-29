-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_iff_of_ofModules
-- name    : AlgebraicGeometry.OModulePresheaf.H0_eq_bot_and_subsingleton_HSucc_iff_of_ofModules
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/199c46db-4e67-51e9-8751-4eae2f910cfc
-- title:
--   Čech vanishing on an ordered affine cover is base-ring independent
-- statement:
--   Let $R_1$ and $R_2$ be commutative rings, $P$ a scheme, and let $\pi_1 : P \to \operatorname{Spec} R_1$ and $\pi_2 : P \to \operatorname{Spec} R_2$ be morphisms of schemes. Let $N$ be a sheaf of $\mathcal{O}_P$-modules and let $\mathfrak{W}$ be an ordered affine cover of $P$, that is, a finite linearly ordered index type together with affine opens $U_i$ of $P$ whose supremum is $\top$. For a morphism $\pi$ as above, `OModulePresheaf.ofModules π N` is the presheaf of $R$-modules on the opens of $P$ given by $U \mapsto \Gamma(N, U)$, with $R$ acting through the ring map $R \to \Gamma(P, U)$ induced by $\pi$ and with the restriction maps of $N$ as ($R$-linear) transition maps; from it one forms the cochain groups $\prod_s \Gamma(N, \mathfrak{W}.\mathrm{inter}\, s)$ indexed by the ordered tuples of degree $i$, with differentials $d^i$, and sets $H^0 = \ker d^0$ and, for $j : \mathbb{N}$, $H^{j+1} = \ker d^{j+1} / \operatorname{im} d^{j}$. The assertion is the equivalence: $H^0 = 0$ and every $H^{j+1}$ is a subsingleton for the presheaf built from $\pi_1$ if and only if the same two conditions hold for the presheaf built from $\pi_2$.
--
--   This records that Čech acyclicity of a sheaf of modules with respect to a fixed ordered affine cover is a property of the underlying complex of abelian groups, hence does not depend on which base ring the sections are read over; it is used to pass between a scheme viewed over a field and over a subfield, and is cited in the construction of polarisations, in [`AlgebraicGeometry.Polarisation.exists_nonempty_tensor_iso_pullback_translate_of_inPicZero_of_kernelPts_finite`](thm.html#AlgebraicGeometry.Polarisation.exists_nonempty_tensor_iso_pullback_translate_of_inPicZero_of_kernelPts_finite).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_iff_of_ofModules.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.H0_eq_bot_and_subsingleton_HSucc_iff_of_ofModules
    {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂] {P : Scheme.{u}}
    (π₁ : P ⟶ Spec (CommRingCat.of R₁)) (π₂ : P ⟶ Spec (CommRingCat.of R₂))
    (N : P.Modules) (𝔚 : P.OrderedAffineCover) :
    ((OModulePresheaf.ofModules π₁ N).H0 𝔚 = ⊥ ∧ ∀ j : ℕ, Subsingleton ((OModulePresheaf.ofModules π₁ N).HSucc 𝔚 j)) ↔
      ((OModulePresheaf.ofModules π₂ N).H0 𝔚 = ⊥ ∧ ∀ j : ℕ, Subsingleton ((OModulePresheaf.ofModules π₂ N).HSucc 𝔚 j)) := by sorry
