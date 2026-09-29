-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_thetaPt_act_eq_iff_exists_translate_comp_toProj_eq
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_thetaPt_act_eq_iff_exists_translate_comp_toProj_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/49f93f72-de0d-5015-8300-5d27ce1a4268
-- title:
--   Theta points versus translations of a framed projective embedding
-- statement:
--   Fix natural numbers $g$, $N$, $n$ and a commutative ring $S$, and let $X$ be a framed polarised abelian scheme of type $(g,N,n)$ over $S$: an abelian scheme $f \colon A \to \operatorname{Spec} S$ with commutative relative group law $L$, fibres of dimension $g$, a basis $P$ of $2g$ $n$-torsion sections, an invertible module $\mathcal{L} = X.\mathrm{pol}$ with geometric fibre $H^0$-rank $N+1$, together with a distinguished projective presentation $X.\mathrm{frame}$ of $\mathcal{L}$ over $f$ by $N+1$ global sections whose associated morphism to $\operatorname{Proj}$ of the graded polynomial ring in $N+1$ variables over $S$ is a closed immersion and whose sections form a section basis on the whole of $A$. Let $P'$ be any further projective presentation of the same module $\mathcal{L}$ along $f$ with $N+1$ sections, i.e. sections $P'.\sigma_i \in \Gamma(\mathcal{L}, \top)$ together with a morphism $P'.\mathrm{toProj}$ over $\operatorname{Spec} S$ satisfying the local freeness and ratio conditions of a presentation. Write $\mathrm{pr}$ for the first projection of the pullback of $f$ along the identity of $\operatorname{Spec} S$. The theorem asserts the equivalence of: (i) there is a theta point $\theta$ for $(f, L, \mathcal{L})$ over the identity test morphism — a section $x$ of $f$ together with an isomorphism between the pullback of $\mathrm{pr}^{*}\mathcal{L}$ along translation by $x$ and $\mathrm{pr}^{*}\mathcal{L}$ — whose action carries $\mathrm{pr}^{*}(X.\mathrm{frame}.\sigma_i)$ to $\mathrm{pr}^{*}(P'.\sigma_i)$ for every $i \in \operatorname{Fin}(N+1)$; and (ii) there is a section $x$ of $f$ over $\operatorname{Spec} S$ such that translation by $x$ followed by $\mathrm{pr}$ followed by $X.\mathrm{frame}.\mathrm{toProj}$ equals $\mathrm{pr}$ followed by $P'.\mathrm{toProj}$.
--
--   This is the dictionary, in Mumford's theta-group formalism, between the action of a theta point on the frame sections of a very ample invertible module and the effect of a translation on the resulting projective embedding: a second presentation of the same module is reached by a theta point exactly when the two morphisms to projective space differ by a translation. It is used in the analysis of theta-adapted pullback squares, in [`AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_ideal_fg_forall_isPullback_isThetaAdapted_iff_map_eq_bot`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_ideal_fg_forall_isPullback_isThetaAdapted_iff_map_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_thetaPt_act_eq_iff_exists_translate_comp_toProj_eq.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_thetaPt_act_eq_iff_exists_translate_comp_toProj_eq
    {g N n : ℕ} {S : Type} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S)
    (P' : Scheme.Modules.ProjPresentation X.pol X.f N) :
    (∃ θ : ThetaPt X.f X.L X.pol (𝟙 (Spec (CommRingCat.of S))), ∀ i : Fin (N + 1),
        θ.act (Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) (X.frame.σ i) :
            Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol, ⊤)) =
          (Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) (P'.σ i) :
            Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol,
              (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) ⁻¹ᵁ ⊤))) ↔
    (∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) X.f,
        Polarisation.translate X.f X.L (𝟙 (Spec (CommRingCat.of S))) x ≫ pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))) ≫
            X.frame.toProj =
          pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))) ≫ P'.toProj) := by sorry
