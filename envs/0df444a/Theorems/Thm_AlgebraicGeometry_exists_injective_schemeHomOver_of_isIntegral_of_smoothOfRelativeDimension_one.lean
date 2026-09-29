-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_injective_schemeHomOver_of_isIntegral_of_smoothOfRelativeDimension_one
-- name    : AlgebraicGeometry.exists_injective_schemeHomOver_of_isIntegral_of_smoothOfRelativeDimension_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/ad249cb4-fe18-5f77-bf19-58ab68df5886
-- title:
--   A smooth integral curve over ̄ k has infinitely many k-points
-- statement:
--   Let $k$ be an algebraically closed field and let $X$ be a scheme, with $f : X \to \operatorname{Spec} k$ a morphism (with $\operatorname{Spec} k$ formed from $k$ viewed as a commutative ring object). Assume that $X$ is an integral scheme, that $f$ is smooth of relative dimension $1$, and that $f$ is locally of finite type. The conclusion is that there is a sequence $x : \mathbb{N} \to \mathtt{SchemeHomOver}\,(\mathbb{1}_{\operatorname{Spec} k})\,f$ which is injective as a function, where the target is by definition the subtype of those morphisms of schemes $\varphi : \operatorname{Spec} k \to X$ such that $\varphi$ followed by $f$ equals the identity of $\operatorname{Spec} k$; that is, the set of sections of $f$, i.e. of $k$-rational points of $X$. So the assertion is that $X(k)$ contains an injective image of $\mathbb{N}$, a concrete form of the statement that $X$ has infinitely many $k$-rational points.
--
--   This is the standard fact that a smooth integral curve of finite type over an algebraically closed field has infinitely many rational points, phrased in terms of sections of the structure morphism. It is used in the construction of sequences of pairwise non-isomorphic objects on quaternionic (fake elliptic curve) moduli, via [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_seq_forall_ne_not_iso_of_not_dvd_of_squarefree`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_seq_forall_ne_not_iso_of_not_dvd_of_squarefree).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_injective_schemeHomOver_of_isIntegral_of_smoothOfRelativeDimension_one.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.exists_injective_schemeHomOver_of_isIntegral_of_smoothOfRelativeDimension_one
    (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] (hf : SmoothOfRelativeDimension 1 f) [LocallyOfFiniteType f] :
    ∃ x : ℕ → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, Function.Injective x := by sorry
