-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_bijective_sum_baseScalar_smul_of_eq_pullbackLocalSection_frame
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.bijective_sum_baseScalar_smul_of_eq_pullbackLocalSection_frame
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/65ba63bf-d3fa-539d-8558-b815b061c1d0
-- title:
--   Pulled-back frame is a basis over the trivial base change
-- statement:
--   Fix naturals $g, N, n$, a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ of nonzero entries, a bijection $e$ between $\mathrm{Fin}(N+1)$ and the finite abelian group $H(\delta) = \prod_i \mathbb{Z}/\delta_i$, a commutative ring $S$, and a framed polarised abelian scheme $X$ of type $(g, N, n)$ over $S$: an abelian scheme $f : A \to \operatorname{Spec} S$ with commutative relative group law, torsion points and invertible polarisation module $\mathrm{pol}$ as in `PolarisedAbelianScheme g (N+1) n S`, together with a projective presentation `X.frame` consisting of $N+1$ global sections $\sigma_i \in \Gamma(\mathrm{pol}, \top)$ and a morphism to $\operatorname{Proj}$ of the polynomial ring over $\operatorname{Spec} S$, the latter a closed immersion, the former a section basis on $\top$ (`frame_basis`). Write $\mathrm{pr} =$ `pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))` for the first projection of the base change along the identity of $\operatorname{Spec} S$. Given a family $\sigma' : H(\delta) \to \Gamma(\mathrm{pr}^*\mathrm{pol}, \top)$ such that $\sigma'_{e(i)}$ equals the pullback `Scheme.Modules.pullbackLocalSection` of $\sigma_i$ for every $i$, the conclusion is that $$c \longmapsto \sum_{h \in H(\delta)} \mathrm{baseScalar}\,f\,\mathrm{id}\,(c_h) \cdot \sigma'_h, \qquad c : H(\delta) \to S,$$ is a bijection onto $\Gamma(\mathrm{pr}^*\mathrm{pol}, \top)$, the scalars acting through the second projection's map on global functions.
--
--   This says that the frame of a framed polarised abelian scheme remains a basis of global sections after the trivial base change, with the index set transported to $H(\delta)$ and scalars acting through the structural morphism of the base-changed scheme; it is the form in which the basis condition is needed in the theta-group formalism. It is used in the results on theta-adapted frames, in particular in the comparison of Schrödinger frames with pullback squares.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_bijective_sum_baseScalar_smul_of_eq_pullbackLocalSection_frame.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.bijective_sum_baseScalar_smul_of_eq_pullbackLocalSection_frame
    {g N n : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    {S : Type} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S)
    (σ' : ((i : Fin g) → ZMod (δ i)) →
      Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol, ⊤))
    (hσ' : ∀ i : Fin (N + 1),
      σ' (e i) =
        (Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) (X.frame.σ i) :
          Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol,
            (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) ⁻¹ᵁ ⊤))) :
    Function.Bijective fun c : ((i : Fin g) → ZMod (δ i)) → S =>
      ∑ h, Polarisation.baseScalar X.f (𝟙 (Spec (CommRingCat.of S))) (c h) • σ' h := by sorry
