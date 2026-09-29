-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_restrict_preimage_basicOpen_of_forall_exists_pow_smul_eq_app
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_restrict_preimage_basicOpen_of_forall_exists_pow_smul_eq_app
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/56c2445b-9221-59e4-bc1c-2b1ed6313149
-- title:
--   Section generating after inverting u trivialises P over h⁻¹D(u)
-- statement:
--   Let $R$ be a commutative ring, $Y$ a scheme and $h : Y \to \operatorname{Spec} R$ a quasi-compact, quasi-separated morphism, and assume that the ring homomorphism $R \to \Gamma(Y, \mathcal O_Y)$ obtained from $h$ on global sections (the inverse of the canonical isomorphism $\Gamma(\operatorname{Spec} R, \mathcal O) \cong R$ followed by `h.appTop`) is bijective. Let $P$ be a module over the structure sheaf of $Y$ which is invertible in the sense of the project predicate `Scheme.Modules.IsInvertible`, that is, every point of $Y$ has an open neighbourhood $U$ such that the pullback of $P$ along the inclusion $U \hookrightarrow Y$ is isomorphic to the unit module of $U$; assume moreover that $P$ is trivial locally on the base: every point $y \in \operatorname{Spec} R$ lies in an open $U$ such that the pullback of $P$ along the inclusion $h^{-1}U \hookrightarrow Y$ is isomorphic to the unit module of $h^{-1}U$. Let $\theta$ be a morphism from the unit module of $Y$ to $P$, and let $u \in R$ be such that every global section $m$ of $P$ satisfies $\mathrm{im}(u^n) \cdot m = \theta_\top(x)$ for some $n \in \mathbb N$ and some global section $x$ of the unit module, the scalar being the image of $u^n$ under the above map $R \to \Gamma(Y,\mathcal O_Y)$. Then the pullback of $\theta$ along the inclusion $h^{-1}(D(u)) \hookrightarrow Y$ is an isomorphism.
--
--   This is the standard statement that an invertible module admitting a global section which generates all global sections after inverting $u$ becomes trivial, via that section, over the preimage of the basic open $D(u)$; the quasi-compactness, quasi-separatedness and the identification $R \cong \Gamma(Y,\mathcal O_Y)$ serve to compute sections over preimages of basic opens as localisations. It is used in the development of the relative Picard functor, where it is cited by [`AlgebraicGeometry.Polarisation.LocIsoOnBase.of_pullback_of_faithfullyFlat_of_isSeparated`](thm.html#AlgebraicGeometry.Polarisation.LocIsoOnBase.of_pullback_of_faithfullyFlat_of_isSeparated).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_restrict_preimage_basicOpen_of_forall_exists_pow_smul_eq_app.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_restrict_preimage_basicOpen_of_forall_exists_pow_smul_eq_app
    {R : Type u} [CommRing R] {Y : Scheme.{u}} (h : Y ⟶ Spec (CommRingCat.of R)) [QuasiCompact h] [QuasiSeparated h]
    (hΓ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ h.appTop).hom)
    (P : Y.Modules) (hP : Scheme.Modules.IsInvertible P)
    (hloc : ∀ y : ↥(Spec (CommRingCat.of R)), ∃ U : (Spec (CommRingCat.of R)).Opens, y ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (h ⁻¹ᵁ U).ι).obj P ≅ SheafOfModules.unit (↑(h ⁻¹ᵁ U) : Scheme.{u}).ringCatSheaf))
    (θ : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ P) (u : R)
    (hgen : ∀ m : Γ(P, ⊤), ∃ (n : ℕ) (x : Γ(SheafOfModules.unit Y.ringCatSheaf, ⊤)),
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ h.appTop).hom (u ^ n)) • m = Scheme.Modules.Hom.app θ ⊤ x) :
    IsIso ((Scheme.Modules.pullback (h ⁻¹ᵁ (PrimeSpectrum.basicOpen u)).ι).map θ) := by sorry
