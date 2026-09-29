-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_kernelTrivial_pullback_inv_of_iso
-- name    : AlgebraicGeometry.Polarisation.kernelTrivial_pullback_inv_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/e62de4ed-0336-528c-9369-381d22383c48
-- title:
--   Trivial Mumford kernel transports along an isomorphism of group laws
-- statement:
--   Let $S$ be a commutative ring, let $A$ and $A'$ be schemes with structure morphisms $f : A \to \operatorname{Spec} S$ and $f' : A' \to \operatorname{Spec} S$, and let $L$, $L'$ be relative group laws for $f$ and $f'$ respectively, i.e. functorial multiplication, unit and inverse operations on the sets $\mathrm{SchemeHomOver}\,t\,f = \{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} S$, satisfying associativity, the unit laws, left inversion and naturality in $T$. Assume given an isomorphism of schemes $e : A \cong A'$ with $f' \circ e = f$ such that for every scheme $T$, every $t : T \to \operatorname{Spec} S$ and all $T$-points $x, y$ of $A$ over $t$ one has $e \circ L.\mathrm{mul}\,t\,x\,y = L'.\mathrm{mul}\,t\,(e\circ x)\,(e\circ y)$, so that $e$ is a homomorphism on points. Let $\mathcal{L}$ be a module over $A$ which is invertible, in the sense that every point of $A$ has an open neighbourhood $U$ on which the restriction of $\mathcal{L}$ is isomorphic to the unit sheaf of modules of $U$. Assume $\mathcal{L}$ has trivial kernel for $(f, L)$: for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} S$ and every point $x$ of $A$ over $t$, if the pullback along the slice morphism $\mathrm{sliceAt}\,f\,x : A \times_{\operatorname{Spec} S} \operatorname{Spec} R \to A \times_{\operatorname{Spec} S} A$ of the Mumford bundle $\mu^{*}\mathcal{L} \otimes (p_1^{*}\mathcal{L}^{\vee} \otimes p_2^{*}\mathcal{L}^{\vee})$ is isomorphic to the unit module locally over the base $\operatorname{Spec} R$ (each point of $\operatorname{Spec} R$ has an open neighbourhood over whose preimage the two pullbacks become isomorphic), then $x = L.\mathrm{one}\,t$. The conclusion is that the transported module $(e^{-1})^{*}\mathcal{L}$ on $A'$ has trivial kernel for $(f', L')$ in the same sense.
--
--   In Mumford's terms this says that the condition $K(\mathcal{L}) = \{e\}$, formulated via the Mumford bundle $\Lambda(\mathcal{L})$ and its slices, is transported along an isomorphism of the two bases' group laws over $\operatorname{Spec} S$. It serves the construction of principal square roots and polarisations, being used in [`AlgebraicGeometry.Polarisation.exists_faithfullyFlat_kernelTrivial_locIsoOnBase_pullback_inv_of_iso`](thm.html#AlgebraicGeometry.Polarisation.exists_faithfullyFlat_kernelTrivial_locIsoOnBase_pullback_inv_of_iso) and in [`AlgebraicGeometry.Polarisation.exists_faithfullyFlat_principalSqrt_of_exists_pullback_of_faithfullyFlat`](thm.html#AlgebraicGeometry.Polarisation.exists_faithfullyFlat_principalSqrt_of_exists_pullback_of_faithfullyFlat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_kernelTrivial_pullback_inv_of_iso.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Polarisation.kernelTrivial_pullback_inv_of_iso
    {S : Type u} [CommRing S] {A A' : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S f')
    (e : A ≅ A') (he : e.hom ≫ f' = f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t f),
      (L.mul t x y).1 ≫ e.hom =
        (L'.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩
          ⟨y.1 ≫ e.hom, by rw [Category.assoc, he]; exact y.2⟩).1)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h : KernelTrivial f L 𝓛) :
    KernelTrivial f' L' ((Scheme.Modules.pullback e.inv).obj 𝓛) := by sorry
