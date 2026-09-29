-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isUnit_forall_app_pullbackLocalSection_frame_eq_baseScalar_smul
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isUnit_forall_app_pullbackLocalSection_frame_eq_baseScalar_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/746651a9-0e4b-586f-ae43-d6daf23e793a
-- title:
--   Base change of a frame agrees up to one unit
-- statement:
--   Fix natural numbers $g, N, n$, commutative rings $S, S'$ and a ring homomorphism $\varphi : S \to S'$, and let $X$ (over $S$) and $X'$ (over $S'$) be framed polarised abelian schemes of type $(g, N, n)$: each consists of a polarised abelian scheme $f : A \to \operatorname{Spec} S$ of relative fibre dimension $g$, with commutative relative group law, $2g$ sections of $n$-torsion forming a basis of the geometric $n$-torsion, an invertible module $\mathcal{L} =$ `pol` very ample by its sections with geometric fibrewise $H^0$-rank $N+1$, together with a $\operatorname{Proj}$ presentation `frame` of $\mathcal{L}$ over $f$ with $N+1$ global sections $\sigma_i$, whose associated morphism to $\mathbb{P}^N_S$ is a closed immersion and whose sections form a section basis on the whole space. Assume given $g_A : A' \to A$ making the square with $f'$, $f$ and $\operatorname{Spec} \varphi$ cartesian, and such that $\iota'$ followed by the base-change map $\mathbb{P}^N_{S'} \to \mathbb{P}^N_S$ (for the $S$-algebra structure on $S'$ given by $\varphi$) equals $g_A$ followed by $\iota$, where $\iota, \iota'$ are the morphisms `frame.toProj`. Assume further given a morphism $b : A' \times_{S'} \operatorname{Spec} S' \to A \times_S \operatorname{Spec} S$ of the trivial test squares, compatible with $g_A$ on first projections and with $\operatorname{Spec}\varphi$ on second projections, and an arbitrary isomorphism of modules $c : b^{*}\mathrm{pr}^{*}\mathcal{L} \cong \mathrm{pr}'^{*}\mathcal{L}'$. Let $\tau_i$ and $\tau'_i$ be the canonical pullbacks (unit of the pullback–pushforward adjunction) of $\sigma_i$ along $\mathrm{pr}$ and of $\sigma'_i$ along $\mathrm{pr}'$. Then there is a unit $u \in S'$ such that for every $i \in \{0, \dots, N\}$ the image under $c$ of the canonical pullback of $\tau_i$ along $b$ equals $u \cdot \tau'_i$, where $u$ acts through the structure map $\mathrm{pr}'$ on global sections (`Polarisation.baseScalar`).
--
--   This is the rigidity statement that a frame (a basis of sections presenting the polarisation projectively) is determined up to a single global unit on the base: after base change along $\varphi$, the transported frame of $X$ and the given frame of $X'$ differ by one unit of $S'$, because both present the same morphism to $\mathbb{P}^N_{S'}$. It is used in the verification that base change of framed polarised abelian schemes is compatible with theta-adaptedness, via [`AlgebraicGeometry.FramedPolarisedAbelianScheme.isThetaAdapted_of_isPullback`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.isThetaAdapted_of_isPullback).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isUnit_forall_app_pullbackLocalSection_frame_eq_baseScalar_smul.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isUnit_forall_app_pullbackLocalSection_frame_eq_baseScalar_smul
    {g N n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (X : FramedPolarisedAbelianScheme g N n S) (X' : FramedPolarisedAbelianScheme g N n S')
    (gA : X'.A ⟶ X.A) (hg : CategoryTheory.IsPullback gA X'.f X.f (Spec.map (CommRingCat.ofHom φ)))
    (hproj : letI : Algebra S S' := φ.toAlgebra; X'.frame.toProj ≫ ProjSpace.map S S' N = gA ≫ X.frame.toProj)
    (b : pullback X'.f (𝟙 (Spec (CommRingCat.of S'))) ⟶ pullback X.f (𝟙 (Spec (CommRingCat.of S))))
    (hb₁ : b ≫ pullback.fst X.f (𝟙 _) = pullback.fst X'.f (𝟙 _) ≫ gA)
    (hb₂ : b ≫ pullback.snd X.f (𝟙 _) = pullback.snd X'.f (𝟙 _) ≫ Spec.map (CommRingCat.ofHom φ))
    (c : (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 _))).obj X.pol) ≅
      (Scheme.Modules.pullback (pullback.fst X'.f (𝟙 _))).obj X'.pol)

    (τ : Fin (N + 1) → Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol, ⊤))
    (hτ : ∀ i : Fin (N + 1), τ i =
      (Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) (X.frame.σ i) :
        Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol,
          (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) ⁻¹ᵁ ⊤)))
    (τ' : Fin (N + 1) → Γ((Scheme.Modules.pullback (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S'))))).obj X'.pol, ⊤))
    (hτ' : ∀ i : Fin (N + 1), τ' i =
      (Scheme.Modules.pullbackLocalSection (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S')))) (X'.frame.σ i) :
        Γ((Scheme.Modules.pullback (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S'))))).obj X'.pol,
          (pullback.fst X'.f (𝟙 (Spec (CommRingCat.of S')))) ⁻¹ᵁ ⊤))) :
    ∃ u : S', IsUnit u ∧ ∀ i : Fin (N + 1),
      c.hom.app ⊤ (Scheme.Modules.pullbackLocalSection b (τ i) :
          Γ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 _))).obj X.pol), ⊤)) =
        Polarisation.baseScalar X'.f (𝟙 (Spec (CommRingCat.of S'))) u • τ' i := by sorry
