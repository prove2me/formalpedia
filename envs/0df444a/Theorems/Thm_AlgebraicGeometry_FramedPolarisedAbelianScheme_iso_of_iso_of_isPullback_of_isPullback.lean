-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_of_iso_of_isPullback_of_isPullback
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_of_iso_of_isPullback_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/d54fb50d-1cb5-5cf5-871f-f6fe95ef8145
-- title:
--   Base change of isomorphic framed polarised abelian schemes
-- statement:
--   Fix natural numbers $g$, $N$, $n$, commutative rings $S$ and $T$ and a ring homomorphism $\varphi : S \to T$. Let $X, X'$ be framed polarised abelian schemes of parameters $(g,N,n)$ over $S$ and $Y, Y'$ such objects over $T$; each consists of a scheme $A$ with a structure morphism to $\operatorname{Spec}$ of the base, a commutative relative group law, the abelian-scheme property bundle, fibres of topological Krull dimension $g$, a family $P : \mathrm{Fin}(2g) \to$ sections killed by $n$ and forming a basis of the $n$-torsion on geometric fibres, an invertible module `pol` which is very ample by its sections and has geometric-fibre $h^0$ equal to $N+1$, and a projective presentation `frame` of `pol` over the base (i.e. $N+1$ global sections together with a morphism $\iota$ to $\mathbb{P}^N$ over $\operatorname{Spec}$ of the base satisfying the frame and ratio conditions), with $\iota$ a closed immersion and the sections a section basis. Assume `Iso X X'`: there is an isomorphism $e : X.A \cong X'.A$ over $\operatorname{Spec} S$ with $e$ followed by $\iota_{X'}$ equal to $\iota_X$, compatible with the group laws on points over any base and with the level sections $P_i$, and such that every point of $\operatorname{Spec} S$ has a neighbourhood $U$ over which the pullback of $X'.\mathrm{pol}$ along $e$ becomes isomorphic to $X.\mathrm{pol}$. Assume further `IsPullback φ X Y` and `IsPullback φ X' Y'`: there are morphisms $g_A : Y.A \to X.A$ and $g_A' : Y'.A \to X'.A$ making the squares with the structure morphisms and $\operatorname{Spec}(\varphi)$ cartesian, compatible with the group laws and with the level sections (each $P_i$ of the $T$-object followed by $g_A$ equals $\operatorname{Spec}(\varphi)$ followed by the corresponding $P_i$ of the $S$-object), with $g_A^{*}(X.\mathrm{pol}) \cong Y.\mathrm{pol}$, and with $\iota_Y$ followed by $\mathbb{P}^N_T \to \mathbb{P}^N_S$ equal to $g_A$ followed by $\iota_X$ (likewise for the primed data). The conclusion is `Iso Y Y'`.
--
--   This is the statement that base change along a fixed ring homomorphism sends isomorphic framed polarised abelian schemes to isomorphic ones, the descent-free half of the functoriality of the framed moduli data. It is used in the analysis of the theta-adapted locus, in particular by [`AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_cover_isReframe_inter_iso_of_isThetaAdapted_of_iso`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_cover_isReframe_inter_iso_of_isThetaAdapted_of_iso) and by [`AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_ideal_fg_isThetaAdapted_iff_eq_bot`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_ideal_fg_isThetaAdapted_iff_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_of_iso_of_isPullback_of_isPullback.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_of_iso_of_isPullback_of_isPullback
    {g N n : ℕ} {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T)
    (X X' : FramedPolarisedAbelianScheme g N n S) (Y Y' : FramedPolarisedAbelianScheme g N n T)
    (hXX' : FramedPolarisedAbelianScheme.Iso X X')
    (hY : FramedPolarisedAbelianScheme.IsPullback φ X Y) (hY' : FramedPolarisedAbelianScheme.IsPullback φ X' Y') :
    FramedPolarisedAbelianScheme.Iso Y Y' := by sorry
