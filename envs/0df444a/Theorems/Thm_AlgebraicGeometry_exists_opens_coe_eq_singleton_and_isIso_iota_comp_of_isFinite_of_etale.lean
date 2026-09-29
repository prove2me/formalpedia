-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_isFinite_of_etale
-- name    : AlgebraicGeometry.exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_isFinite_of_etale
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/4e9f3833-5eca-5573-a57c-a435f036c938
-- title:
--   Finite étale schemes over an algebraically closed field split
-- statement:
--   Let $k$ be an algebraically closed field, $X$ a scheme, and $f : X \to \operatorname{Spec} k$ a morphism of schemes (with $\operatorname{Spec} k$ the spectrum of $k$ viewed as a commutative ring object) which is finite and étale, and let $x$ be a point of $X$. The assertion is that there exists an open subscheme $U$ of $X$ whose underlying set is exactly the singleton $\{x\}$ and such that the composite of the canonical open immersion $U.\iota : U \to X$ with $f$ is an isomorphism of schemes, i.e. $U \xrightarrow{\sim} \operatorname{Spec} k$. In particular every point of such an $X$ is open, and the corresponding one-point open subscheme is a copy of $\operatorname{Spec} k$; the statement is the pointwise form of the decomposition $X = \coprod_{x \in X} \operatorname{Spec} k$, which is not itself asserted here.
--
--   This is the standard structure theorem for finite étale schemes over a separably (here algebraically) closed field, in the form needed to identify geometric points of such a scheme with its points. It is used in the treatment of formally unramified morphisms over algebraically closed fields, in the analysis of level structures on fake elliptic curves in the Čerednik–Drinfel'd setting, and in the study of torsion sections of abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_isFinite_of_etale.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_isFinite_of_etale
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsFinite f] [Etale f] (x : X) :
    ∃ U : X.Opens, (U : Set X) = {x} ∧ IsIso (U.ι ≫ f) := by sorry
