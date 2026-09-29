-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_mem_and_iota_comp_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq
-- name    : AlgebraicGeometry.exists_mem_and_iota_comp_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/adae7b22-430c-5d7d-a219-62025da5096c
-- title:
--   Agreement on all jets at a point implies agreement near it
-- statement:
--   Let $X$ and $Y$ be schemes (in a fixed universe), with $X$ locally Noetherian, let $f, g \colon X \to Y$ be two morphisms of schemes, and let $x$ be a point of $X$. Write $\mathcal{O}_{X,x}$ for the stalk `X.presheaf.stalk x`, a local ring with maximal ideal $\mathfrak{m}_x$, and let `X.fromSpecStalk x` be the canonical morphism $\operatorname{Spec}\mathcal{O}_{X,x} \to X$. The hypothesis is that for every natural number $n$ the morphism $\operatorname{Spec}(\mathcal{O}_{X,x}/\mathfrak{m}_x^{\,n}) \to \operatorname{Spec}\mathcal{O}_{X,x}$ induced by the quotient map, followed by `X.fromSpecStalk x` and then by $f$, coincides with the same composite formed with $g$ in place of $f$; that is, $f$ and $g$ agree on every infinitesimal neighbourhood $\operatorname{Spec}(\mathcal{O}_{X,x}/\mathfrak{m}_x^{\,n})$ of $x$, including the degenerate case $n = 0$. The conclusion asserts the existence of an open subscheme $U$ of $X$ (an element of `X.Opens`) such that $x \in U$ and the open immersion $U.ι \colon U \to X$ followed by $f$ equals $U.ι$ followed by $g$, i.e. $f$ and $g$ restrict to the same morphism $U \to Y$.
--
--   This is the local, Krull-intersection half of the rigidity principle for morphisms out of a locally Noetherian scheme: two morphisms inducing the same map on all jets $\mathcal{O}_{X,x}/\mathfrak{m}_x^{\,n}$ at a point already agree on a neighbourhood of that point. It is used in the proof of [`AlgebraicGeometry.eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq_of_isSchemeTheoreticallyDominant`](thm.html#AlgebraicGeometry.eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq_of_isSchemeTheoreticallyDominant), where agreement near one point is propagated to all of $X$ by a dominance hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_mem_and_iota_comp_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_mem_and_iota_comp_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f g : X ⟶ Y) (x : X)
    (h : ∀ n : ℕ,
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n))) ≫ X.fromSpecStalk x ≫ f =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n))) ≫ X.fromSpecStalk x ≫ g) :
    ∃ U : X.Opens, x ∈ U ∧ U.ι ≫ f = U.ι ≫ g := by sorry
