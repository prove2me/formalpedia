-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isProper_notMem_ringKrullDim_stalk_eq_one_of_not_isProper
-- name    : AlgebraicGeometry.exists_isProper_notMem_ringKrullDim_stalk_eq_one_of_not_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/7c42f9ec-1c5e-5e20-afbd-16eb00876b05
-- title:
--   Making the boundary of a normal complete model divisorial
-- statement:
--   Let $k$ be a field and let $f : X \to \operatorname{Spec} k$ be a morphism of schemes with $X$ integral, $f$ separated, locally of finite type and quasi-compact, and assume $f$ is not proper. Let $p : P \to \operatorname{Spec} k$ be proper with $P$ integral and with every local ring $\mathcal{O}_{P,y}$ integrally closed; let $D$ be an open subscheme of $P$ and $\tau : D \to X$ a proper morphism with $\tau$ followed by $f$ equal to the open immersion $D \hookrightarrow P$ followed by $p$; and let $V$ be a non-empty open subscheme of $X$ together with an open immersion $\iota : V \to D$ such that $\iota$ followed by $\tau$ is the inclusion $V \hookrightarrow X$. Then there exist a scheme $P'$, a morphism $\pi : P' \to P$, an open subscheme $V'$ of $X$ and a morphism $\iota' : V' \to \pi^{-1}(D)$ such that: $P'$ is integral and all its local rings are integrally closed; $\pi$ is proper; $V'$ is non-empty; $\iota'$ is an open immersion; $\iota'$ followed by the restriction $\pi \mid_D : \pi^{-1}(D) \to D$ and then by $\tau$ is the inclusion $V' \hookrightarrow X$; and there is a point $w \in P'$ lying outside the open set $\pi^{-1}(D)$ with $\operatorname{ringKrullDim} \mathcal{O}_{P',w} = 1$.
--
--   This is Rosenlicht's lemma preceding his theorem on the completion of a variety: a normal complete model $(P,D,\tau,V,\iota)$ of a non-proper $X$ may be replaced, after a proper modification $\pi : P' \to P$ which is again normal and again dominates $X$ over a non-empty open set, by one whose boundary contains a point of local dimension one, i.e. a divisorial component. It is used in the construction of compatible stable partial actions on Jacobians, via [`GoodReductionJacobian.PartialAction.exists_compatible_stable_defined_one_of_not_isProper`](thm.html#GoodReductionJacobian.PartialAction.exists_compatible_stable_defined_one_of_not_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isProper_notMem_ringKrullDim_stalk_eq_one_of_not_isProper.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isProper_notMem_ringKrullDim_stalk_eq_one_of_not_isProper
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hX : ¬ IsProper f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsProper p] [IsIntegral P]
    (hn : ∀ y : P, IsIntegrallyClosed (P.presheaf.stalk y))
    (D : P.Opens) (τ : (D : Scheme.{u}) ⟶ X) [IsProper τ] (hτ : τ ≫ f = D.ι ≫ p)
    (V : X.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ (D : Scheme.{u}))
    [IsOpenImmersion ι] (hτι : ι ≫ τ = V.ι) :
    ∃ (P' : Scheme.{u}) (π : P' ⟶ P) (V' : X.Opens)
      (ι' : (V' : Scheme.{u}) ⟶ (π ⁻¹ᵁ D : Scheme.{u})),
      IsIntegral P' ∧ (∀ y : P', IsIntegrallyClosed (P'.presheaf.stalk y)) ∧ IsProper π ∧
      Nonempty (V' : Scheme.{u}) ∧ IsOpenImmersion ι' ∧ ι' ≫ (π ∣_ D) ≫ τ = V'.ι ∧
      ∃ w : P', w ∉ (π ⁻¹ᵁ D : Set P') ∧ ringKrullDim (P'.presheaf.stalk w) = 1 := by sorry
