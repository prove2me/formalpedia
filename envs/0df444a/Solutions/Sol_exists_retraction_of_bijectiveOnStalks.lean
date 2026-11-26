-- Prove2me | solution 1 for exists_retraction_of_bijectiveOnStalks
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-26T19:43:02.257814+00:00
-- url     : https://prove2.me/submissions/3e9d9430-5f0f-4241-b5ff-cd19952407ff

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.FiniteType
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.GroupWithZero.Pi
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Ring.Fin
import Mathlib.Algebra.Ring.Pi
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.Presentation
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Sites.Hypercover.Zero
import Mathlib.CategoryTheory.WithTerminal.Cone
import Mathlib.CategoryTheory.WithTerminal.Lemmas
import Mathlib.Data.Set.Card
import Mathlib.FieldTheory.Extension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.Logic.Function.Basic
import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.Pure
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalIso
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.OpenImmersion
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.RingHom.Surjective
import Mathlib.RingTheory.RingHomProperties
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Tactic.Algebraize
import Mathlib.Tactic.DepRewrite
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.Stonean.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Constructions
import Mathlib.Topology.DiscreteQuotient
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Inseparable
import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Sober
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Topology.Spectral.Hom
import Mathlib.Topology.Spectral.Prespectral
import Definitions.Def_ProEtale_Algebra_Bijective
import Definitions.Def_ProEtale_Algebra_Contraction_Covers
import Definitions.Def_ProEtale_Algebra_Etale
import Definitions.Def_ProEtale_Algebra_Etale_Lib
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat_Lib
import Definitions.Def_ProEtale_Algebra_HenselianLocalRing
import Definitions.Def_ProEtale_Algebra_Ind
import Definitions.Def_ProEtale_Algebra_IndEtale
import Definitions.Def_ProEtale_Algebra_IndEtale_Lib
import Definitions.Def_ProEtale_Algebra_IndWeaklyEtale
import Definitions.Def_ProEtale_Algebra_IndWeaklyEtale_Lib
import Definitions.Def_ProEtale_Algebra_IndZariski
import Definitions.Def_ProEtale_Algebra_IntegralLocal
import Definitions.Def_ProEtale_Algebra_LocalIso
import Definitions.Def_ProEtale_Algebra_LocalizationColimit
import Definitions.Def_ProEtale_Algebra_ProEtaleContraction
import Definitions.Def_ProEtale_Algebra_PullbackProfinite
import Definitions.Def_ProEtale_Algebra_RetractionsStrictlyHenselian
import Definitions.Def_ProEtale_Algebra_StalkAlgebraic
import Definitions.Def_ProEtale_Algebra_StalkIso
import Definitions.Def_ProEtale_Algebra_WContractible
import Definitions.Def_ProEtale_Algebra_WLocal
import Definitions.Def_ProEtale_Algebra_WLocal_Lib
import Definitions.Def_ProEtale_Algebra_WLocalization_Basic
import Definitions.Def_ProEtale_Algebra_WLocalization_Ideal
import Definitions.Def_ProEtale_Algebra_WStrictLocalization
import Definitions.Def_ProEtale_Algebra_WeakDimension
import Definitions.Def_ProEtale_Algebra_WeaklyEtale
import Definitions.Def_ProEtale_Algebra_WeaklyEtale_Lib
import Definitions.Def_ProEtale_Algebra_WeaklyEtaleField
import Definitions.Def_ProEtale_FiniteFields_Etale_AlgebraicHenselization
import Definitions.Def_ProEtale_FiniteFields_Etale_IndEtale
import Definitions.Def_ProEtale_FiniteFields_Etale_IndEtaleStructural
import Definitions.Def_ProEtale_FromPi1_Etale
import Definitions.Def_ProEtale_Mathlib_Algebra_Algebra_Pi
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_AlgCat_FilteredColimits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits_Lib
import Definitions.Def_ProEtale_Mathlib_Algebra_GroupWithZero_NonZeroDivisors
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_ShortComplex_Exact
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_FilteredColimitCommutesProduct
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Preserves_Shapes_Zero
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Shapes_FiniteLimits
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Shapes_WidePullbacks
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Composition
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_IndSpreads
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_ObjectProperty_FiniteProducts
import Definitions.Def_ProEtale_Mathlib_FieldTheory_IsSepClosed
import Definitions.Def_ProEtale_Mathlib_Logic_Function_Basic
import Definitions.Def_ProEtale_Mathlib_Order_BooleanAlgebra_Set
import Definitions.Def_ProEtale_Mathlib_RingTheory_Etale_Field
import Definitions.Def_ProEtale_Mathlib_RingTheory_Etale_Henselian
import Definitions.Def_ProEtale_Mathlib_RingTheory_Etale_Prod
import Definitions.Def_ProEtale_Mathlib_RingTheory_Flat_FaithfullyFlat_Basic
import Definitions.Def_ProEtale_Mathlib_RingTheory_Henselian
import Definitions.Def_ProEtale_Mathlib_RingTheory_Henselian_Lib
import Definitions.Def_ProEtale_Mathlib_RingTheory_Ideal_GoingDown
import Definitions.Def_ProEtale_Mathlib_RingTheory_Ideal_Pure
import Definitions.Def_ProEtale_Mathlib_RingTheory_Idempotents
import Definitions.Def_ProEtale_Mathlib_RingTheory_IntegralClosure_IntegrallyClosed
import Definitions.Def_ProEtale_Mathlib_RingTheory_Localization_Pi
import Definitions.Def_ProEtale_Mathlib_RingTheory_RingHom_Etale
import Definitions.Def_ProEtale_Mathlib_RingTheory_Spectrum_Prime_RingHom
import Definitions.Def_ProEtale_Mathlib_RingTheory_Spectrum_Prime_Topology
import Definitions.Def_ProEtale_Mathlib_RingTheory_TensorProduct_Maps
import Definitions.Def_ProEtale_Mathlib_RingTheory_WeaklyEtale_Localization
import Definitions.Def_ProEtale_Mathlib_Topology_Category_TopCat_Limits_Pullbacks
import Definitions.Def_ProEtale_Mathlib_Topology_Connected_TotallyDisconnected
import Definitions.Def_ProEtale_Mathlib_Topology_Constructions
import Definitions.Def_ProEtale_Mathlib_Topology_Inseparable
import Definitions.Def_ProEtale_Mathlib_Topology_JacobsonSpace
import Definitions.Def_ProEtale_Mathlib_Topology_QuasiSeparated
import Definitions.Def_ProEtale_Mathlib_Topology_Separation_Basic
import Definitions.Def_ProEtale_Mathlib_Topology_Separation_Hausdorff
import Definitions.Def_ProEtale_Mathlib_Topology_Sober
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Basic
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_ConstructibleTopology
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Prespectral
import Definitions.Def_ProEtale_Topology_Preliminaries_Profinite
import Definitions.Def_ProEtale_Topology_Preliminaries_Pullback
import Definitions.Def_ProEtale_Topology_SpectralSpace_ConnectedComponent
import Definitions.Def_ProEtale_Topology_SpectralSpace_Constructible
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Basic
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Basic_Lib
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_ClosedPoints
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_ConnectedComponents
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Pullback
import Definitions.Def_ProEtale_Algebra_WContractible_Lib
import Theorems.Thm_IsWLocalRing_of_surjective
import Theorems.Thm_RingHom_BijectiveOnStalks_comp

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

/-!
# w-contractible rings

A ring is w-contractible if it is w-strictly-local and the space of connected components of
its prime spectrum is extremally disconnected.

Every w-contractible ring is indeed contractible in the ind-étale topology in the following
sense: If `R` is w-contractible, then every ind-étale faithfully flat map `R →+* S`
has a retraction.

The ind-étale site has enough contractible objects, in the sense that every ring admits a
faithfully flat, ind-étale algebra that is w-contractible.
-/

universe u


open PrimeSpectrum TopologicalSpace


section Retraction

open WContractification Topology

variable {R : Type u} [CommRing R]

/-- Auxiliary step for `exists_retraction_of_bijectiveOnStalks`: if `R → S` is a map of
w-local rings that is bijective on stalks, maps closed points of `Spec S` to closed points of
`Spec R`, and if there is a closed subset `T ⊆ π₀(Spec S)` mapping bijectively onto
`π₀(Spec R)`, then `R → S` has a retraction. The retraction is obtained by restricting `S` to
the components in `T` (via `WContractification.Restriction`) and showing that the resulting
map `R → Restriction T` is bijective. -/
private theorem exists_retraction_of_isClosed_of_bijOn [IsWLocalRing R]
    {S : Type u} [CommRing S] [Algebra R S] [IsWLocalRing S]
    (hbos : (algebraMap R S).BijectiveOnStalks)
    (hcl : ∀ y ∈ closedPoints (PrimeSpectrum S),
      PrimeSpectrum.comap (algebraMap R S) y ∈ closedPoints (PrimeSpectrum R))
    (T : Set (ConnectedComponents (PrimeSpectrum S))) (hT : IsClosed T)
    (hsurjT : ∀ c : ConnectedComponents (PrimeSpectrum R), ∃ t ∈ T,
      (PrimeSpectrum.continuous_comap (algebraMap R S)).connectedComponentsMap t = c)
    (hinjT : ∀ t₁ ∈ T, ∀ t₂ ∈ T,
      (PrimeSpectrum.continuous_comap (algebraMap R S)).connectedComponentsMap t₁ =
        (PrimeSpectrum.continuous_comap (algebraMap R S)).connectedComponentsMap t₂ →
      t₁ = t₂) :
    ∃ f : S →+* R, f.comp (algebraMap R S) = RingHom.id R := by
  letI : Algebra R (Restriction T) := Algebra.compHom _ (algebraMap R S)
  haveI : IsScalarTower R S (Restriction T) := .of_algebraMap_eq' rfl
  haveI : IsWLocalRing (Restriction T) :=
    .of_surjective (Restriction.algebraMap_surjective T)
  -- The triangle of spectra commutes.
  have htower : ∀ w : PrimeSpectrum (Restriction T),
      PrimeSpectrum.comap (algebraMap R (Restriction T)) w =
        PrimeSpectrum.comap (algebraMap R S)
          (PrimeSpectrum.comap (algebraMap S (Restriction T)) w) := fun w ↦ by
    rw [← PrimeSpectrum.comap_comp_apply, ← IsScalarTower.algebraMap_eq]
  -- `Spec (Restriction T) → Spec S` is a closed embedding with range `mk ⁻¹' T`.
  have hε : IsClosedEmbedding (PrimeSpectrum.comap (algebraMap S (Restriction T))) :=
    Restriction.isClosedEmbedding_algebraMap_specComap
  have hrange : Set.range (PrimeSpectrum.comap (algebraMap S (Restriction T))) =
      ConnectedComponents.mk ⁻¹' T :=
    Restriction.range_algebraMap_specComap hT
  -- The range is stable under specialization, being a union of connected components.
  have hstable : StableUnderSpecialization
      (Set.range (PrimeSpectrum.comap (algebraMap S (Restriction T)))) := by
    rw [hrange]
    intro x y hxy hx
    rw [Set.mem_preimage] at hx ⊢
    rwa [← hxy.connectedComponents_mk_eq]
  -- Hence `Spec (Restriction T) → Spec S` maps closed points to closed points.
  have hεcl : ∀ w ∈ closedPoints (PrimeSpectrum (Restriction T)),
      PrimeSpectrum.comap (algebraMap S (Restriction T)) w ∈
        closedPoints (PrimeSpectrum S) := fun w hw ↦
    mem_closedPoints_iff.mpr
      (hε.isEmbedding.isClosed_singleton hstable (mem_closedPoints_iff.mp hw))
  -- Points of `Spec (Restriction T)` lie in components belonging to `T`.
  have hmkT : ∀ w : PrimeSpectrum (Restriction T),
      ConnectedComponents.mk (PrimeSpectrum.comap (algebraMap S (Restriction T)) w) ∈ T := by
    intro w
    have hmem : PrimeSpectrum.comap (algebraMap S (Restriction T)) w ∈
        Set.range (PrimeSpectrum.comap (algebraMap S (Restriction T))) :=
      Set.mem_range_self w
    rwa [hrange] at hmem
  -- Compatibility of the two `π₀`-maps.
  have hπcomm : ∀ w : PrimeSpectrum (Restriction T),
      (PrimeSpectrum.continuous_comap (algebraMap R S)).connectedComponentsMap
        (ConnectedComponents.mk (PrimeSpectrum.comap (algebraMap S (Restriction T)) w)) =
      ConnectedComponents.mk (PrimeSpectrum.comap (algebraMap R (Restriction T)) w) := by
    intro w
    rw [Continuous.connectedComponentsMap_mk, htower]
  -- The algebra map `R → Restriction T` is a w-local ring map.
  have hwlocal : (algebraMap R (Restriction T)).IsWLocal := by
    refine ⟨PrimeSpectrum.isSpectralMap_comap _, fun w hw ↦ ?_⟩
    rw [Set.mem_preimage, htower]
    exact hcl _ (hεcl w hw)
  -- It is bijective on stalks.
  have hbosB : (algebraMap R (Restriction T)).BijectiveOnStalks := by
    rw [IsScalarTower.algebraMap_eq R S (Restriction T)]
    exact hbos.comp (Algebra.IndZariski.bijectiveOnStalks_algebraMap S (Restriction T))
  -- It is bijective on connected components.
  have hbijπ₀ : Function.Bijective
      (PrimeSpectrum.continuous_comap (algebraMap R (Restriction T))).connectedComponentsMap := by
    constructor
    · -- Injectivity: every component of the w-local `Spec (Restriction T)` contains a
      -- unique closed point; images of these closed points in `π₀(Spec S)` lie in `T`,
      -- where the comparison with `π₀(Spec R)` is injective by assumption.
      intro c₁ c₂ heq
      obtain ⟨⟨w₁, hw₁⟩, hc₁⟩ :=
        (WLocalSpace.isHomeomorph_connectedComponents_closedPoints
          (PrimeSpectrum (Restriction T))).bijective.2 c₁
      obtain ⟨⟨w₂, hw₂⟩, hc₂⟩ :=
        (WLocalSpace.isHomeomorph_connectedComponents_closedPoints
          (PrimeSpectrum (Restriction T))).bijective.2 c₂
      rw [← hc₁, ← hc₂] at heq ⊢
      have heq' : ConnectedComponents.mk
            (PrimeSpectrum.comap (algebraMap R (Restriction T)) w₁) =
          ConnectedComponents.mk
            (PrimeSpectrum.comap (algebraMap R (Restriction T)) w₂) := heq
      have hkey : PrimeSpectrum.comap (algebraMap S (Restriction T)) w₁ =
          PrimeSpectrum.comap (algebraMap S (Restriction T)) w₂ :=
        WLocalSpace.closedPoints_eq_of_mk_eq (hεcl w₁ hw₁) (hεcl w₂ hw₂)
          (hinjT _ (hmkT w₁) _ (hmkT w₂) (by rw [hπcomm w₁, hπcomm w₂, heq']))
      have hw : w₁ = w₂ := hε.injective hkey
      subst hw
      rfl
    · -- Surjectivity: a component of `Spec R` is hit by some `t ∈ T`, and `mk ⁻¹' T` is
      -- the range of `Spec (Restriction T) → Spec S`.
      intro c
      obtain ⟨t, htT, hπt⟩ := hsurjT c
      obtain ⟨x₀, hx₀⟩ := ConnectedComponents.surjective_coe t
      have hx₀mem : x₀ ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Restriction T))) := by
        rw [hrange, Set.mem_preimage, hx₀]
        exact htT
      obtain ⟨w, hw⟩ := hx₀mem
      refine ⟨ConnectedComponents.mk w, ?_⟩
      calc (PrimeSpectrum.continuous_comap
            (algebraMap R (Restriction T))).connectedComponentsMap (ConnectedComponents.mk w)
          = ConnectedComponents.mk (PrimeSpectrum.comap (algebraMap R (Restriction T)) w) :=
            Continuous.connectedComponentsMap_mk _ w
        _ = (PrimeSpectrum.continuous_comap (algebraMap R S)).connectedComponentsMap
            (ConnectedComponents.mk (PrimeSpectrum.comap (algebraMap S (Restriction T)) w)) :=
            (hπcomm w).symm
        _ = c := by rw [hw, hx₀]; exact hπt
  -- Conclude: `R → Restriction T` is bijective, and inverting it gives the retraction.
  have hbij : Function.Bijective (algebraMap R (Restriction T)) :=
    hwlocal.bijective_of_bijective hbosB hbijπ₀
  let e : R ≃+* Restriction T := RingEquiv.ofBijective _ hbij
  refine ⟨(e.symm : Restriction T →+* R).comp (algebraMap S (Restriction T)), ?_⟩
  refine RingHom.ext fun r ↦ ?_
  change e.symm (algebraMap S (Restriction T) (algebraMap R S r)) = r
  rw [← IsScalarTower.algebraMap_apply R S (Restriction T)]
  exact e.symm_apply_apply r

/-- Stacks 09AZ (second part of the proof of (3) => (1)), blueprint
`thm:ff-identifies-local-rings-plus-c-has-retraction-if`: a faithfully flat map identifying
local rings from a w-local ring with extremally disconnected π₀ to a w-local ring whose
closed points are cut out by the pulled-back ideal has a retraction. -/
@[stacks 09AZ "second part of the proof of (3) => (1)"]
theorem exists_retraction_of_bijectiveOnStalks [IsWLocalRing R]
    [ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum R))]
    {I : Ideal R} (hI : zeroLocus (I : Set R) = closedPoints (PrimeSpectrum R))
    {S : Type u} [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    [Algebra.BijectiveOnStalks R S] [IsWLocalRing S]
    (hS : zeroLocus ((I.map (algebraMap R S) : Ideal S) : Set S) =
      closedPoints (PrimeSpectrum S)) :
    ∃ f : S →+* R, f.comp (algebraMap R S) = RingHom.id R := by
  -- Closed points of `Spec S` lie over closed points of `Spec R`.
  have hcl : ∀ y ∈ closedPoints (PrimeSpectrum S),
      PrimeSpectrum.comap (algebraMap R S) y ∈ closedPoints (PrimeSpectrum R) := by
    intro y hy
    rw [← hS, mem_zeroLocus] at hy
    rw [← hI, mem_zeroLocus]
    intro a ha
    exact Ideal.mem_comap.mpr (hy (Ideal.mem_map_of_mem _ ha))
  -- `π₀(Spec S) → π₀(Spec R)` admits a continuous section by Gleason's theorem, since the
  -- target is extremally disconnected and the map is surjective by faithful flatness.
  obtain ⟨ρ, hρcont, hρ⟩ :=
    (CompactT2.ExtremallyDisconnected.projective
        (A := ConnectedComponents (PrimeSpectrum R)))
      continuous_id
      (PrimeSpectrum.continuous_comap (algebraMap R S)).connectedComponentsMap_continuous
      ((PrimeSpectrum.continuous_comap (algebraMap R S)).connectedComponentsMap_surjective
        PrimeSpectrum.comap_surjective_of_faithfullyFlat)
  -- The range of the section is a closed set of components mapping bijectively onto
  -- `π₀(Spec R)`.
  refine exists_retraction_of_isClosed_of_bijOn
    (RingHom.bijectiveOnStalks_algebraMap.mpr ‹_›) hcl (Set.range ρ)
    (isCompact_range hρcont).isClosed
    (fun c ↦ ⟨ρ c, Set.mem_range_self c, congrFun hρ c⟩) ?_
  rintro _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ h
  have h₁ := congrFun hρ c₁
  have h₂ := congrFun hρ c₂
  simp only [Function.comp_apply, id_eq] at h₁ h₂
  rw [h₁, h₂] at h
  rw [h]

end Retraction

variable {R : Type u} [CommRing R]


variable (R)


theorem solution.{sol_u1} : type_of% @exists_retraction_of_bijectiveOnStalks.{sol_u1} := @exists_retraction_of_bijectiveOnStalks.{sol_u1}
