-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_AffineProEt_exists_singleton_refinement
-- name    : AlgebraicGeometry.Scheme.AffineProEt.exists_singleton_refinement
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:15:15.96417+00:00
-- url     : https://prove2.me/theorems/55aab044-f612-5b20-8cb3-ec2c6a6e7ffa
-- title:
--   Every pro-étale covering sieve of an affine pro-étale object is refined by a surjection whose source splits into finitely many disjoint opens
-- statement:
--   Let $S$ be a scheme and $U_0$ an object of the affine pro-étale site of $S$ (a scheme whose structure map to $S$ is a cofiltered limit of affine étale $S$-schemes). Let $R$ be a sieve on the image of $U_0$ in the pro-étale site $S_{\mathrm{pro\acute et}}$ which is a covering sieve for the pro-étale topology. Then there exist
--
--   - an object $W$ of the affine pro-étale site and a morphism $q : W \to U_0$ whose underlying morphism of schemes is surjective,
--   - a finite index type $\iota$, objects $V_k$ ($k\in\iota$) of the affine pro-étale site and morphisms $j_k : V_k \to W$,
--
--   such that
--   1. for every $k$, the composite $q\circ j_k : V_k \to U_0$ (viewed in $S_{\mathrm{pro\acute et}}$) belongs to $R$;
--   2. every $j_k$ is an open immersion of schemes;
--   3. the images of the $j_k$ cover $W$;
--   4. the images of the $j_k$ are pairwise disjoint.
--
--   Thus, schematically,
--   $$\textstyle\coprod_{k\in\iota} V_k \;\cong\; W \xrightarrow{\;q\;} U_0, \qquad q\circ j_k \in R \text{ for all } k,$$
--   with $q$ surjective. This reduction lets one replace an arbitrary covering sieve of an affine pro-étale object by a single surjective map followed by a finite disjoint open decomposition, which is the shape needed for Čech-type vanishing arguments (Cartan's criterion) on the affine pro-étale site.
--
--   **Formalization Note** Here `S : Scheme.{u}`, objects are `S.AffineProEt`, and the sieve lives on `(AffineProEt.toProEt S).obj U₀` in `S.ProEt` with the topology `ProEt.topology S`. Surjectivity is the scheme morphism property `Surjective q.left`; the index type is `ι : Type u` with a `Finite` instance supplied as an existential witness. Covering and disjointness are stated via `Set.range` of the underlying continuous maps of `(j k).left`. The fork labels this step **(D1)**. The disjoint union in the display above is only an informal paraphrase of conditions 2–4; the Lean statement does not construct a coproduct.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Comparison/Acyclicity.lean, lines 176-201 (`AlgebraicGeometry.Scheme.AffineProEt.exists_singleton_refinement`).

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.FiniteType
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Limits
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
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Ring.Fin
import Mathlib.Algebra.Ring.Pi
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Cover.Sigma
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.AlgebraicGeometry.Sites.Pretopology
import Mathlib.AlgebraicGeometry.Sites.Small
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct
import Mathlib.CategoryTheory.Limits.Indization.Category
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Limits.MonoCoprod
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.Presentation
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.CategoryTheory.Presentable.Basic
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.CoproductSheafCondition
import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.Hypercover.Saturate
import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Hypercover.Zero
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.MorphismProperty
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Precoverage.Subsheaf
import Mathlib.CategoryTheory.Sites.Preserves
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.WithTerminal.Cone
import Mathlib.CategoryTheory.WithTerminal.Lemmas
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Sum
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
import Mathlib.Topology.Sets.CompactOpenCovered
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Sober
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Topology.Spectral.Hom
import Mathlib.Topology.Spectral.Prespectral
import Definitions.Def_ProEtale_Comparator_Definitions
import Definitions.Def_ProEtale_Comparator_Lib
import Definitions.Def_ProEtale_Algebra_Bijective
import Definitions.Def_ProEtale_Algebra_Contraction_Covers
import Definitions.Def_ProEtale_Algebra_Etale
import Definitions.Def_ProEtale_Algebra_Etale_Lib
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat_Lib
import Definitions.Def_ProEtale_Algebra_HenselianLocalRing
import Definitions.Def_ProEtale_Algebra_IdentifiesLocalRings
import Definitions.Def_ProEtale_Algebra_Ind
import Definitions.Def_ProEtale_Algebra_IndBijectiveOnStalks
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
import Definitions.Def_ProEtale_Algebra_WContractible_Lib
import Definitions.Def_ProEtale_Algebra_WLocal
import Definitions.Def_ProEtale_Algebra_WLocal_Lib
import Definitions.Def_ProEtale_Algebra_WLocalization_Basic
import Definitions.Def_ProEtale_Algebra_WLocalization_Ideal
import Definitions.Def_ProEtale_Algebra_WStrictLocalization
import Definitions.Def_ProEtale_Algebra_WeakDimension
import Definitions.Def_ProEtale_Algebra_WeaklyEtale
import Definitions.Def_ProEtale_Algebra_WeaklyEtale_Lib
import Definitions.Def_ProEtale_Algebra_WeaklyEtaleField
import Definitions.Def_ProEtale_Algebra_WeaklyEtaleIndEtale
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
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_AffineTransitionLimit
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Cover_MorphismProperty
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Extensive
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Morphisms_UnderlyingMap
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Sites_AffineEtale
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Sites_AffineRefinement
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Sites_Small
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Comma_ArrowRefinement
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Comma_StructuredArrow_Basic
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Comma
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_FilteredColimitCommutesProduct
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_MorphismProperty
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Preserves_Shapes_Zero
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Shapes_FiniteLimits
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Shapes_WidePullbacks
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Basic
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Composition
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_IndSpreads
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Limits
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_ObjectProperty_FiniteProducts
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_DenseSubsite_Basic
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_Finite
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_Grothendieck
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_MorphismProperty
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_Pullback
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_SheafCohomology_CechResolution
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_SheafCohomology_FreeAbelianSheaf
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_SheafCohomology_LocallyVanish
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_Sheafification
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_Sieves
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
import Definitions.Def_ProEtale_Mathlib_RingTheory_LocalRing_RingHom_Basic
import Definitions.Def_ProEtale_Mathlib_RingTheory_Localization_Pi
import Definitions.Def_ProEtale_Mathlib_RingTheory_RingHom_Etale
import Definitions.Def_ProEtale_Mathlib_RingTheory_Spectrum_Prime_Localization
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
import Definitions.Def_ProEtale_Morphisms_ProAffineEtale
import Definitions.Def_ProEtale_Morphisms_ProAffineEtale_Lib
import Definitions.Def_ProEtale_Morphisms_WeaklyEtale
import Definitions.Def_ProEtale_Morphisms_WeaklyEtale_Lib
import Definitions.Def_ProEtale_Pro_Basic
import Definitions.Def_ProEtale_Pro_Basic_Lib
import Definitions.Def_ProEtale_Pro_Generating
import Definitions.Def_ProEtale_Pro_PresheafColimit
import Definitions.Def_ProEtale_Topology_Coherent_Affine
import Definitions.Def_ProEtale_Topology_Coherent_Etale
import Definitions.Def_ProEtale_Topology_Comparison_Affine
import Definitions.Def_ProEtale_Topology_Comparison_Affine_Lib
import Definitions.Def_ProEtale_Topology_Comparison_CechColimit
import Definitions.Def_ProEtale_Topology_Comparison_FreeSheaf
import Definitions.Def_ProEtale_Topology_Comparison_SectionsColimit
import Definitions.Def_ProEtale_Topology_Flat_QuasiCompactCover
import Definitions.Def_ProEtale_Topology_LocalProperties
import Definitions.Def_ProEtale_Topology_Preliminaries_Profinite
import Definitions.Def_ProEtale_Topology_Preliminaries_Pullback
import Definitions.Def_ProEtale_Topology_Proetale_Basic
import Definitions.Def_ProEtale_Topology_Proetale_Sheafification
import Definitions.Def_ProEtale_Topology_Proetale_Sheafification_Lib
import Definitions.Def_ProEtale_Topology_SpectralSpace_ConnectedComponent
import Definitions.Def_ProEtale_Topology_SpectralSpace_Constructible
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Basic
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Basic_Lib
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_ClosedPoints
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_ConnectedComponents
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Pullback
import Definitions.Def_ProEtale_Topology_Comparison_Acyclicity

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits Opposite Abelian

open scoped Simplicial

namespace AlgebraicGeometry
namespace Scheme

variable {S : Scheme.{u}}

namespace AffineProEt

theorem exists_singleton_refinement (U₀ : S.AffineProEt)
    {R : Sieve ((AffineProEt.toProEt S).obj U₀)}
    (hR : R ∈ ProEt.topology S ((AffineProEt.toProEt S).obj U₀)) :
    ∃ (W : S.AffineProEt) (q : W ⟶ U₀) (ι : Type u) (_ : Finite ι)
      (V : ι → S.AffineProEt) (j : ∀ k, V k ⟶ W),
      Surjective q.left ∧
      (∀ k, R.arrows ((AffineProEt.toProEt S).map (j k ≫ q))) ∧
      (∀ k, IsOpenImmersion (j k).left) ∧
      (∀ x : W.left, ∃ k, x ∈ Set.range ((j k).left.base)) ∧
      (Pairwise fun k l ↦ Disjoint (Set.range ((j k).left.base))
        (Set.range ((j l).left.base))) := by sorry

end AffineProEt

variable (S)

end Scheme
end AlgebraicGeometry
