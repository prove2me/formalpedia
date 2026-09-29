-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_baseChange_chart_isPullback_of_isPullback
-- name    : AlgebraicGeometry.exists_baseChange_chart_isPullback_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/f29844ad-7e2a-5820-93a1-caa8eadec06f
-- title:
--   Base change of an affine chart on an open subscheme
-- statement:
--   Let $O$, $K$, $Q$ be commutative rings in a single universe with $K$ and $Q$ given as $O$-algebras, and let $X$, $X_K$ be schemes. Given morphisms $\mathrm{toO} \colon X \to \operatorname{Spec} O$, $\mathrm{toK} \colon X_K \to \operatorname{Spec} K$ and $\mathrm{pr} \colon X_K \to X$, assume the square formed by $\mathrm{pr}$, $\mathrm{toK}$, $\mathrm{toO}$ and $\operatorname{Spec}$ of the structure map $O \to K$ is cartesian, that is, $\mathrm{pr}$ followed by $\mathrm{toO}$ equals $\mathrm{toK}$ followed by $\operatorname{Spec}(O \to K)$, and this square exhibits $X_K$ as $X \times_{\operatorname{Spec} O} \operatorname{Spec} K$. Let $U$ be an open subscheme of $X$ and $f \colon U \to \operatorname{Spec} Q$ a morphism over $O$, in the sense that $f$ followed by $\operatorname{Spec}(O \to Q)$ equals the open immersion $U \hookrightarrow X$ followed by $\mathrm{toO}$. The conclusion asserts the existence of a morphism $f_K \colon \mathrm{pr}^{-1}(U) \to \operatorname{Spec}(K \otimes_O Q)$, on the open subscheme $\mathrm{pr}^{-1}(U)$ of $X_K$, such that: $f_K$ followed by $\operatorname{Spec}$ of $q \mapsto 1 \otimes q$ equals the restricted morphism $\mathrm{pr}\mid_U \colon \mathrm{pr}^{-1}(U) \to U$ followed by $f$; $f_K$ followed by $\operatorname{Spec}$ of $K \to K \otimes_O Q$ equals the open immersion $\mathrm{pr}^{-1}(U) \hookrightarrow X_K$ followed by $\mathrm{toK}$; and the square with sides $f_K$, $\mathrm{pr}\mid_U$, $\operatorname{Spec}(q \mapsto 1 \otimes q)$ and $f$ is cartesian.
--
--   This is the standard compatibility of an affine chart on an open subscheme with base change: a chart $f \colon U \to \operatorname{Spec} Q$ over $O$ induces a chart $f_K$ on $\mathrm{pr}^{-1}(U)$ over $\operatorname{Spec}(K \otimes_O Q)$, and the inducing square is cartesian, so that properties of $f$ stable under base change (for instance étaleness) transfer to $f_K$. It is used in the construction of charts on the base change of a model of a modular curve at $p$, both to produce an étale chart after base change and in the computation of a valuation read off from such a chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_baseChange_chart_isPullback_of_isPullback.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.exists_baseChange_chart_isPullback_of_isPullback
    {O K Q : Type u} [CommRing O] [CommRing K] [CommRing Q] [Algebra O Q] [Algebra O K]
    {X XK : Scheme.{u}} (toO : X ⟶ Spec (CommRingCat.of O)) (toK : XK ⟶ Spec (CommRingCat.of K)) (pr : XK ⟶ X)
    (hpr : IsPullback pr toK toO (Spec.map (CommRingCat.ofHom (algebraMap O K))))
    (U : X.Opens) (f : (U : Scheme.{u}) ⟶ Spec (CommRingCat.of Q))
    (hover : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O Q)) = U.ι ≫ toO) :
    ∃ fK : ((pr ⁻¹ᵁ U : XK.Opens) : Scheme.{u}) ⟶ Spec (CommRingCat.of (K ⊗[O] Q)),
      fK ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := O) (A := K) (B := Q)).toRingHom) = (pr ∣_ U) ≫ f ∧
      fK ≫ Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[O] Q))) = (pr ⁻¹ᵁ U).ι ≫ toK ∧
      IsPullback fK (pr ∣_ U) (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := O) (A := K) (B := Q)).toRingHom)) f := by sorry
