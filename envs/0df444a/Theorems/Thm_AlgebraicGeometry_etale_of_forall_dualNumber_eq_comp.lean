-- Prove2me | Theorems.Thm_AlgebraicGeometry_etale_of_forall_dualNumber_eq_comp
-- name    : AlgebraicGeometry.etale_of_forall_dualNumber_eq_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/da6a65cb-4208-5038-8897-b12c411f0e35
-- title:
--   Dual-number criterion for étaleness over an algebraically closed field
-- statement:
--   Let $\kappa$ be an algebraically closed field and let $f_K \colon K \to \operatorname{Spec}\kappa$ be a morphism of schemes that is locally of finite type, where $\operatorname{Spec}\kappa$ is the spectrum of $\kappa$ regarded as a commutative ring. Write $\kappa[\varepsilon] = \kappa \oplus \kappa\varepsilon$ with $\varepsilon^2 = 0$ for the ring of dual numbers over $\kappa$, let $\pi \colon \operatorname{Spec}\kappa[\varepsilon] \to \operatorname{Spec}\kappa$ be the morphism induced by the structure map $\kappa \to \kappa[\varepsilon]$, and let $\iota \colon \operatorname{Spec}\kappa \to \operatorname{Spec}\kappa[\varepsilon]$ be the morphism induced by the $\kappa$-algebra map $\kappa[\varepsilon] \to \kappa$, $a + b\varepsilon \mapsto a$. Assume that every $\kappa[\varepsilon]$-valued point of $K$ lying over $\pi$ is constant, in the sense that for each $v \colon \operatorname{Spec}\kappa[\varepsilon] \to K$ with $v$ followed by $f_K$ equal to $\pi$ one has $v = v \circ \iota \circ \pi$ (that is, $\pi$ followed by $\iota$ followed by $v$ equals $v$). Then $f_K$ is étale.
--
--   This is the tangent-space form of the criterion for a scheme locally of finite type over an algebraically closed field to be étale over that field: vanishing of all Zariski tangent vectors at all points, expressed by the factorisation of dual-number points through their base points, forces the structure morphism to be étale. It is used to establish étaleness of a base-changed projection, and in the modular-curve setting to deduce reducedness of a fibre obtained by pullback.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_etale_of_forall_dualNumber_eq_comp.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.etale_of_forall_dualNumber_eq_comp
    {κ : Type u} [Field κ] [IsAlgClosed κ] {K : Scheme.{u}} (fK : K ⟶ Spec (CommRingCat.of κ)) [LocallyOfFiniteType fK]
    (h : ∀ v : Spec (CommRingCat.of (DualNumber κ)) ⟶ K,
      v ≫ fK = Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) →
      v = Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) ≫
            Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ).toRingHom) ≫ v) :
    Etale fK := by sorry
