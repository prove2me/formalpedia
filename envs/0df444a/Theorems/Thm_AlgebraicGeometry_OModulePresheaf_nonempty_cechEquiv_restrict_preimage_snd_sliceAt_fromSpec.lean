-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_restrict_preimage_snd_sliceAt_fromSpec
-- name    : AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_restrict_preimage_snd_sliceAt_fromSpec
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/c41ce339-08b8-5404-89be-e17a052c859c
-- title:
--   Čech cohomology of a strip equals that of the slice
-- statement:
--   Let $k$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} k$ a separated morphism. Let $F$ be an $\mathcal{O}$-module on $A \times_k A =$ `pullback f f` which is invertible in the sense that every point of that scheme has an open neighbourhood $U$ with $(\,\cdot\,)|_U$-pullback of $F$ isomorphic to the unit module of $U$; let $\mathcal{U}$ be an ordered affine cover of $A$ (a finite linearly ordered family of affine opens with supremum $\top$); let $V \subseteq A$ be an open with $V$ affine, and $W$ an open of $A \times_k A$ equal to the preimage of $V$ under the second projection, equipped with an ordered affine cover $\mathfrak{W}$ of $W$ viewed as a scheme. Put $S := \Gamma(A, V)$, let $\sigma : \operatorname{Spec} S \to A$ be the canonical morphism attached to the affine open $V$, $t_S := \sigma$ followed by $f$, and regard $\sigma$ as a morphism over $t_S$. Let $F_S$ be the pullback of $F$ along `sliceAt f ⟨σ, rfl⟩` $: A \times_k \operatorname{Spec} S \to A \times_k A$, and $\mathcal{U}_S$ the cover of $A \times_k \operatorname{Spec} S$ whose members are the preimages of those of $\mathcal{U}$ under the first projection (affine, the projection being affine). Let $G_S$ be the $\mathcal{O}$-module presheaf $U \mapsto \Gamma(F_S, U)$ with its $S$-structure coming from the second projection $A \times_k \operatorname{Spec} S \to \operatorname{Spec} S$, and $G_W$ the presheaf $U \mapsto \Gamma(F|_W, U)$ with its $k$-structure coming from $W \hookrightarrow A \times_k A \to A \to \operatorname{Spec} k$. With $S$ a $k$-algebra through $f$ and $V$, and the Čech modules of $G_S$ regarded as $k$-modules by restriction of scalars along $k \to S$, the assertion is that there exists a $k$-linear isomorphism $G_W.\mathrm{H0}(\mathfrak{W}) \cong G_S.\mathrm{H0}(\mathcal{U}_S)$ and, for every $q \in \mathbb{N}$, a $k$-linear isomorphism between the corresponding $q$-th higher Čech modules `HSucc`, i.e. $\ker d_{q+1}$ modulo the image of $d_q$, for the two covers. The isomorphisms are asserted to exist (as nonempty types), not constructed canonically.
--
--   This is the comparison showing that the Čech cohomology of an invertible module on the strip $p_2^{-1}(V) \subseteq A \times_k A$ over an affine open $V \subseteq A$ agrees, $k$-linearly and for arbitrary ordered affine covers on either side, with that of the slice family $A \times_k \operatorname{Spec} \Gamma(V, \mathcal{O}_A)$ with the sliced module. It is the base-change step used in the finiteness and rank computations for the Čech cohomology of the slice in the construction of the polarisation pairing, and is obtained from the transport of Čech cohomology along an isomorphism of schemes together with an isomorphism of modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_restrict_preimage_snd_sliceAt_fromSpec.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_restrict_preimage_snd_sliceAt_fromSpec
    {k : Type u} [CommRing k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k)) [IsSeparated f]
    (F : (pullback f f).Modules) (hF : Scheme.Modules.IsInvertible F)
    (𝒰 : A.OrderedAffineCover) (V : A.Opens) (hV : IsAffineOpen V)
    (W : (pullback f f).Opens) (hW : W = (pullback.snd f f) ⁻¹ᵁ V)
    (𝔚 : (W : Scheme.{u}).OrderedAffineCover) :
    letI S : Type u := ↥Γ(A, V)
    letI σ : Spec (CommRingCat.of S) ⟶ A := hV.fromSpec
    letI tS : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of k) := σ ≫ f
    letI xS : SchemeHomOver tS f := ⟨σ, rfl⟩
    letI FS : (pullback f tS).Modules := (Scheme.Modules.pullback (sliceAt f xS)).obj F
    letI _ : IsAffineHom (pullback.fst f tS) := MorphismProperty.pullback_fst _ _ inferInstance
    letI 𝒰S : (pullback f tS).OrderedAffineCover := 𝒰.comap (pullback.fst f tS)
    letI GS := OModulePresheaf.ofModules (pullback.snd f tS) FS
    letI GW := OModulePresheaf.ofModules (W.ι ≫ pullback.fst f f ≫ f) (F.restrict W.ι)
    letI _ : Algebra k S := Scheme.TwoAffineOpenCover.algebraOfHom f V
    letI _ : Module k ↥(GS.H0 𝒰S) := Module.compHom _ (algebraMap k S)
    letI _ : ∀ q : ℕ, Module k (GS.HSucc 𝒰S q) := fun q => Module.compHom _ (algebraMap k S)
    Nonempty (↥(GW.H0 𝔚) ≃ₗ[k] ↥(GS.H0 𝒰S)) ∧
      ∀ q : ℕ, Nonempty (GW.HSucc 𝔚 q ≃ₗ[k] GS.HSucc 𝒰S q) := by sorry
