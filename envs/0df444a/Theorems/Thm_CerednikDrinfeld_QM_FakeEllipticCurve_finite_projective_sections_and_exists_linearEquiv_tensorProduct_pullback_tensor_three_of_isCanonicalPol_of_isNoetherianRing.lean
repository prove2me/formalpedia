-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_finite_projective_sections_and_exists_linearEquiv_tensorProduct_pullback_tensor_three_of_isCanonicalPol_of_isNoetherianRing
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.finite_projective_sections_and_exists_linearEquiv_tensorProduct_pullback_tensor_three_of_isCanonicalPol_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/641e8ec9-1900-57af-b071-9bff62fae5f2
-- title:
--   Finite projectivity and base change for L^{⊗ 3}
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and a commutative Noetherian ring $S$. Let $E$ be a fake elliptic curve of level data $(\Lambda,N)$ over $S$, that is, a structure consisting of a scheme $E.A$ with a morphism $E.f : E.A \to \operatorname{Spec} S$, a commutative relative group law, an abelian-scheme property bundle, fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms over $S$ compatible with the group law and with prescribed traces, and the further level-structure data of the structure. Let $\mathrm{star} : \Lambda \to \Lambda$ be a function and $\mathcal{L}$ an object of the category of modules on $E.A$ satisfying the predicate `IsCanonicalPolData` for $E.f$, the group law, the $\Lambda$-action together with its compatibility with $E.f$, and $\mathrm{star}$; the first component of that predicate asserts that $\mathcal{L}$ is invertible. Write $M := \mathcal{L} \otimes \mathcal{L} \otimes \mathcal{L}$. Then two things hold. First, equipping the global sections $\Gamma(M, \top)$ with the $S$-module structure obtained by restriction of scalars along the isomorphism $S \cong \Gamma(\operatorname{Spec} S, \mathcal{O})$ followed by the map on top sections induced by $E.f$, the module $\Gamma(M, \top)$ is finite and projective over $S$. Second, for every commutative ring $S'$, every ring homomorphism $\varphi : S \to S'$, and every scheme $A'$ with morphisms $f' : A' \to \operatorname{Spec} S'$ and $g_A : A' \to E.A$ forming a pullback square with $E.f$ and $\operatorname{Spec}(\varphi)$, the $S'$-module $\Gamma(g_A^{*}M, g_A^{-1}\top)$ — with the structure coming from $S' \cong \Gamma(\operatorname{Spec} S',\mathcal{O})$ followed by the map induced by $f'$ on the relevant opens — admits, for the $S$-algebra structure on $S'$ given by $\varphi$, an $S'$-linear isomorphism $e : S' \otimes_S \Gamma(M,\top) \to \Gamma(g_A^{*}M, g_A^{-1}\top)$ with $e(s' \otimes \tau) = s' \cdot \mathrm{pullbackLocalSection}\,g_A\,\tau$ for all $s' \in S'$ and $\tau \in \Gamma(M,\top)$, where $\mathrm{pullbackLocalSection}$ is the section obtained from the unit of the pullback–pushforward adjunction for $g_A$.
--
--   This is cohomology and base change in degree $0$ for the cube of the canonical polarisation of a fake elliptic curve over a Noetherian base: the sections of $\mathcal{L}^{\otimes 3}$ form a finitely generated projective module whose formation commutes with arbitrary base change. It is used to produce the projective embedding of the abelian surface by sections of $\mathcal{L}^{\otimes 3}$, in `closedImmersionBySections_tensor_three_of_isCanonicalPol_of_isNoetherianRing`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_finite_projective_sections_and_exists_linearEquiv_tensorProduct_pullback_tensor_three_of_isCanonicalPol_of_isNoetherianRing.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.finite_projective_sections_and_exists_linearEquiv_tensorProduct_pullback_tensor_three_of_isCanonicalPol_of_isNoetherianRing
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] [IsNoetherianRing S]
    (E : FakeEllipticCurve Λ N S) (star : ↥Λ → ↥Λ) (𝓛 : E.A.Modules) (h𝓛 : E.IsCanonicalPol star 𝓛) :
    (letI : Module S Γ((𝓛 ⊗ 𝓛 ⊗ 𝓛), ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ E.f.appTop).hom
     Module.Finite S Γ((𝓛 ⊗ 𝓛 ⊗ 𝓛), ⊤) ∧ Module.Projective S Γ((𝓛 ⊗ 𝓛 ⊗ 𝓛), ⊤)) ∧
    ∀ (S' : Type) [CommRing S'] (φ : S →+* S')
      (A' : Scheme.{0}) (f' : A' ⟶ Spec (CommRingCat.of S')) (gA : A' ⟶ E.A)
      (hg : CategoryTheory.IsPullback gA f' E.f (Spec.map (CommRingCat.ofHom φ))),
      letI : Module S Γ((𝓛 ⊗ 𝓛 ⊗ 𝓛), ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ E.f.appTop).hom
      letI : Module S' Γ((Scheme.Modules.pullback gA).obj (𝓛 ⊗ 𝓛 ⊗ 𝓛), gA ⁻¹ᵁ ⊤) :=
        Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (gA ⁻¹ᵁ ⊤) le_top).hom
      letI : Algebra S S' := φ.toAlgebra
      ∃ e : S' ⊗[S] Γ((𝓛 ⊗ 𝓛 ⊗ 𝓛), ⊤) ≃ₗ[S'] Γ((Scheme.Modules.pullback gA).obj (𝓛 ⊗ 𝓛 ⊗ 𝓛), gA ⁻¹ᵁ ⊤),
        ∀ (s' : S') (τ : Γ((𝓛 ⊗ 𝓛 ⊗ 𝓛), ⊤)), e (s' ⊗ₜ[S] τ) = s' • Scheme.Modules.pullbackLocalSection gA τ := by sorry
