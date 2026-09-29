-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_ideal_fg_forall_isPullback_exists_comp_toProj_eq_one_comp_iff_map_eq_bot
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_ideal_fg_forall_isPullback_exists_comp_toProj_eq_one_comp_iff_map_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/e7805030-45c3-5fa1-bad8-3cc7587f1241
-- title:
--   Finitely generated ideal detecting a translating point
-- statement:
--   Let $g,N,n$ be natural numbers, $S$ a commutative ring and $X$ a framed polarised abelian scheme of type $(g,N+1,n)$ over $S$: an abelian scheme $f : A \to \operatorname{Spec} S$ with commutative relative group law, all fibres of dimension $g$, a basis $P_1,\dots,P_{2g}$ of $n$-torsion sections, an invertible module `pol` whose geometric fibre $H^0$ has rank $N+1$, together with a frame, i.e. a `ProjPresentation` consisting of $N+1$ global sections $\sigma_i$ of `pol` and a morphism $\iota = X.\mathtt{frame}.\mathtt{toProj} : A \to \mathbb P^N_S$ over $\operatorname{Spec} S$ compatible with the $\sigma_i$, with $\iota$ a closed immersion and $\sigma$ a section basis. Let $U$ be an invertible $(N+1)\times(N+1)$ matrix over $S$. The assertion is that there is a finitely generated ideal $J \subseteq S$ such that for every commutative ring $T$, every ring homomorphism $\varphi : S \to T$, every framed polarised abelian scheme $Y$ of the same type over $T$ which is a pullback of $X$ along $\varphi$ (a cartesian square over $\operatorname{Spec}\varphi$ compatible with the group laws, matching the torsion sections, identifying the pulled-back polarisation, and with $Y.\mathtt{frame}.\mathtt{toProj}$ followed by $\mathbb P^N_T \to \mathbb P^N_S$ equal to the structure map followed by $\iota$), and every `ProjPresentation` $P'$ of $Y.\mathtt{pol}$ over $Y.f$ of the same size whose sections satisfy $P'.\sigma_i = \sum_j \varphi(U_{ij})\,Y.\mathtt{frame}.\sigma_j$ (the scalars acting through the structure morphism on global sections), one has: there exists a section $x$ of $Y.f$ with $x$ followed by $Y.\mathtt{frame}.\mathtt{toProj}$ equal to the identity section of $Y.L$ followed by $P'.\mathtt{toProj}$ if and only if $\varphi(J)$ generates the zero ideal of $T$.
--
--   This is the point-existence step of the construction of conditional ideals for framed polarised abelian schemes: the condition that, after a linear change of frame by $U$, the zero section lands in the image of the frame embedding is cut out, uniformly in all base changes, by a single finitely generated ideal of $S$. It is used in the corresponding statement about the existence of a translating morphism, [`AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_ideal_fg_forall_isPullback_exists_translate_comp_eq_iff_map_eq_bot`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_ideal_fg_forall_isPullback_exists_translate_comp_eq_iff_map_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_ideal_fg_forall_isPullback_exists_comp_toProj_eq_one_comp_iff_map_eq_bot.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_ideal_fg_forall_isPullback_exists_comp_toProj_eq_one_comp_iff_map_eq_bot
    {g N n : ℕ} {S : Type} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S)
    (U : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (hU : IsUnit U) :
    ∃ J : Ideal S, J.FG ∧ ∀ (T : Type) [CommRing T] (φ : S →+* T) (Y : FramedPolarisedAbelianScheme g N n T),
      FramedPolarisedAbelianScheme.IsPullback φ X Y →
      ∀ (P' : Scheme.Modules.ProjPresentation Y.pol Y.f N),
        (∀ i : Fin (N + 1), P'.σ i =
          ∑ j : Fin (N + 1), ((Y.f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom (φ (U i j)))) • Y.frame.σ j) →
        ((∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of T))) Y.f, x.1 ≫ Y.frame.toProj = (Y.L.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ P'.toProj) ↔
          J.map φ = ⊥) := by sorry
