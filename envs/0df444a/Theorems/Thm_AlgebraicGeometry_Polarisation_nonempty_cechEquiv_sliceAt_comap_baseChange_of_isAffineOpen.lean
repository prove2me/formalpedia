-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_cechEquiv_sliceAt_comap_baseChange_of_isAffineOpen
-- name    : AlgebraicGeometry.Polarisation.nonempty_cechEquiv_sliceAt_comap_baseChange_of_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/384a36e5-e548-50bd-982e-d5cb91d5273a
-- title:
--   Slice Čech cohomology versus base change of an affine chart
-- statement:
--   Let $K$ be a field, let $f : A \to \operatorname{Spec} K$ be a separated morphism of schemes, and let $F$ be a module on the fibre product $A \times_{\operatorname{Spec} K} A$ (the pullback of $f$ along itself) which is invertible in the sense that every point of that product has an open neighbourhood on which the restriction of $F$ is isomorphic to the unit sheaf of modules. Let $\mathcal K$ be an ordered affine cover of $A$, i.e. a finite linearly ordered family of affine opens with supremum $\top$, let $V$ be an affine open of $A$, let $B$ be a commutative ring with a $\Gamma(A,V)$-algebra structure, let $t : \operatorname{Spec} B \to \operatorname{Spec} K$ be a morphism, and let $x$ be a morphism $\operatorname{Spec} B \to A$ with $x \circ f$ (in diagrammatic order, $x$ followed by $f$) equal to $t$, subject to the hypothesis that $x$ is the morphism $\operatorname{Spec} B \to \operatorname{Spec} \Gamma(A,V)$ induced by the algebra map, followed by the canonical immersion $\operatorname{Spec} \Gamma(A,V) \to A$ of the affine open $V$. Put $t_V :=$ the immersion of $V$ followed by $f$, regard the immersion as a point $x_V$ of $A$ over $t_V$, and let $\pi$ be the second projection $A \times_{\operatorname{Spec} K} V \to \operatorname{Spec} \Gamma(A,V)$ and $M_V$ the pullback of $F$ along the slice map $\mathrm{sliceAt}\ f\ x_V = (\mathrm{fst}, \mathrm{snd}\ \text{followed by}\ x_V)$. Let $\mathcal U$ be the cover of $A \times_{\operatorname{Spec} K} V$ obtained by taking preimages of the members of $\mathcal K$ under the first projection. Let $G$ be the $\mathcal O$-module presheaf on $A \times_{\operatorname{Spec} K} \operatorname{Spec} B$ attached, via the projection to $\operatorname{Spec} B$, to the pullback of $F$ along $\mathrm{sliceAt}\ f\ x$, and let $G'$ be the $\mathcal O$-module presheaf attached, via the projection to $\operatorname{Spec} B$, to the pullback of $M_V$ along the first projection of $(A \times_{\operatorname{Spec} K} V) \times_{\operatorname{Spec} \Gamma(A,V)} \operatorname{Spec} B$. The conclusion asserts the existence of a $B$-linear isomorphism between the degree-zero ordered Čech group $H^0$ of $G$ for the preimage cover $\mathcal K$ under the first projection and that of $G'$ for the base-changed cover $\mathcal U$ along $\operatorname{Spec} B \to \operatorname{Spec} \Gamma(A,V)$, together with, for every $i \in \mathbb N$, a $B$-linear isomorphism between the corresponding groups $\ker d^{i+1}/\operatorname{im} d^{i}$ of the two Čech complexes.
--
--   This is the compatibility statement identifying the "slice" presentation of the Čech cohomology of an invertible module on $A \times_K A$ restricted over a test scheme $\operatorname{Spec} B$ with its "base change" presentation over an affine chart $V$ of the second factor, the two presentations used respectively in the torsion and length computations and in the perfect-complex/base-change machinery. It is obtained from the transport principle [`AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso_pullback_of_isIso`](thm.html#AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso_pullback_of_isIso) for isomorphisms over the base, and is used by the statements on torsion of Čech stalks, on finiteness and rank of Čech modules along a strip, and on vanishing of localised Čech modules outside the image.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_cechEquiv_sliceAt_comap_baseChange_of_isAffineOpen.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.nonempty_cechEquiv_sliceAt_comap_baseChange_of_isAffineOpen
    (K : Type) [Field K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K)) [IsSeparated f]
    (F : (pullback f f).Modules) (hF : Scheme.Modules.IsInvertible F)
    (𝒦 : A.OrderedAffineCover) (V : A.Opens) (hV : IsAffineOpen V)
    (B : Type) [CommRing B] [Algebra Γ(A, V) B]
    (t : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f)
    (hx : x.1 = Scheme.TwoAffineOpenCover.specMap Γ(A, V) B ≫ hV.fromSpec) :
    letI tV : Spec (CommRingCat.of Γ(A, V)) ⟶ Spec (CommRingCat.of K) := hV.fromSpec ≫ f
    letI xV : SchemeHomOver tV f := ⟨hV.fromSpec, rfl⟩
    letI π : pullback f tV ⟶ Spec (CommRingCat.of Γ(A, V)) := pullback.snd f tV
    letI MV : (pullback f tV).Modules := (Scheme.Modules.pullback (sliceAt f xV)).obj F
    letI _ : IsAffineHom (pullback.fst f tV) := MorphismProperty.pullback_fst _ _ inferInstance
    letI _ : IsAffineHom (pullback.fst f t) := MorphismProperty.pullback_fst _ _ inferInstance
    letI 𝒰 : (pullback f tV).OrderedAffineCover := 𝒦.comap (pullback.fst f tV)
    letI G := OModulePresheaf.ofModules (pullback.snd f t) ((Scheme.Modules.pullback (sliceAt f x)).obj F)
    letI G' := OModulePresheaf.ofModules (pullback.snd π (Scheme.TwoAffineOpenCover.specMap Γ(A, V) B))
      ((Scheme.Modules.pullback (pullback.fst π (Scheme.TwoAffineOpenCover.specMap Γ(A, V) B))).obj MV)
    Nonempty (G.H0 (𝒦.comap (pullback.fst f t)) ≃ₗ[B] G'.H0 (𝒰.baseChange π B)) ∧
      ∀ i : ℕ, Nonempty (G.HSucc (𝒦.comap (pullback.fst f t)) i ≃ₗ[B] G'.HSucc (𝒰.baseChange π B) i) := by sorry
