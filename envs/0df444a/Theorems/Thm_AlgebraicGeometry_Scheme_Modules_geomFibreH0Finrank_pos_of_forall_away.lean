-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_pos_of_forall_away
-- name    : AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_pos_of_forall_away
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/7801218b-359d-58d7-9fca-c0a573ab3018
-- title:
--   Positivity of geometric-fibre h⁰ is local on the base
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism. Let $r : \mathrm{Fin}\,k \to S$ be a finite family whose range generates the unit ideal of $S$. For each index $i$ let $A'_i$ be a scheme with a morphism $f'_i : A'_i \to \operatorname{Spec} S[1/r_i]$ (the localisation away from $r_i$) and a morphism $g_i : A'_i \to A$ such that the square formed by $g_i$, $f'_i$, $f$ and the morphism $\operatorname{Spec} S[1/r_i] \to \operatorname{Spec} S$ induced by the localisation map is cartesian. Let $\mathcal L$ be a module on $A$. Assume that for every $i$, every algebraically closed field $K$ and every ring homomorphism $s' : S[1/r_i] \to K$, the quantity `Scheme.Modules.geomFibreH0Finrank` of $f'_i$ and the pullback $g_i^{*}\mathcal L$ at $(K, s')$ is strictly positive; that is, the $K$-dimension of the global sections of the pullback of $g_i^{*}\mathcal L$ to the fibre product $A'_i \times_{\operatorname{Spec} S[1/r_i]} \operatorname{Spec} K$ is nonzero. Then for every algebraically closed field $K$ and every ring homomorphism $s : S \to K$, the corresponding $K$-dimension for $f$ and $\mathcal L$ is strictly positive.
--
--   This records that strict positivity of $h^0$ on geometric fibres of a module is a property local on the base for a covering of $\operatorname{Spec} S$ by basic opens. It is used in the verification that canonical polarisation data can be glued from a distinguished affine cover, via [`CerednikDrinfeld.QM.IsCanonicalPolData.of_forall_away`](thm.html#CerednikDrinfeld.QM.IsCanonicalPolData.of_forall_away).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_pos_of_forall_away.lean

import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

universe u v

theorem AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_pos_of_forall_away
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (A' : Fin k → Scheme.{u}) (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (Localization.Away (r i))))
    (g : ∀ i, A' i ⟶ A)
    (hg : ∀ i, IsPullback (g i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i))))))
    (𝓛 : A.Modules)
    (hloc : ∀ (i : Fin k) (K : Type u) [Field K] [IsAlgClosed K] (sk' : Localization.Away (r i) →+* K),
      0 < Scheme.Modules.geomFibreH0Finrank (f' i) ((Scheme.Modules.pullback (g i)).obj 𝓛) K sk') :
    ∀ (K : Type u) [Field K] [IsAlgClosed K] (sk : S →+* K), 0 < Scheme.Modules.geomFibreH0Finrank f 𝓛 K sk := by sorry
