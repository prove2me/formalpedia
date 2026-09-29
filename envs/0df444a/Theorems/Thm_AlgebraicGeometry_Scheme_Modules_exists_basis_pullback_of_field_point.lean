-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_basis_pullback_of_field_point
-- name    : AlgebraicGeometry.Scheme.Modules.exists_basis_pullback_of_field_point
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/dd11f449-93d0-5208-8106-1882b376dcaa
-- title:
--   Local basis remains a basis after pull-back to a field point
-- statement:
--   Let $X$ be a scheme, $M$ a sheaf of $\mathcal{O}_X$-modules on $X$, $n$ a natural number, $U$ an open subset of $X$, and let $e \colon \mathrm{Fin}\, n \to \Gamma(M,U)$ be a family of sections of $M$ over $U$. Assume that for every open $W \subseteq U$ there is a basis of the $\Gamma(X,W)$-module $\Gamma(M,W)$ indexed by $\mathrm{Fin}\, n$ whose $i$-th member is the restriction of $e_i$ to $W$; that is, the restricted family $(e_i|_W)_i$ is a basis of $\Gamma(M,W)$. Let $K$ be a field, $s \colon \operatorname{Spec} K \to X$ a morphism of schemes, and suppose the image under $s$ of the closed point of $\operatorname{Spec} K$ lies in $U$. Then there is a basis of the $\Gamma(\operatorname{Spec} K, s^{-1}U)$-module $\Gamma((s^{*}M), s^{-1}U)$, indexed by $\mathrm{Fin}\, n$, whose $i$-th member is the image of $e_i$ under the component at $U$ of the unit of the adjunction between pull-back along $s$ and push-forward along $s$, viewed as a section of $s^{*}M$ over $s^{-1}U$.
--
--   This says that the fibre of a sheaf of modules at a $K$-valued point is free on the values of any local basis defined near the image point, the basis being exhibited by the unit of the pull-back/push-forward adjunction; no local freeness of $M$ beyond the given basis on $U$, and no hypothesis on $X$, is assumed. It is used in the criterion [`AlgebraicGeometry.Scheme.Modules.exists_pullbackSection_dual_det_eq_zero_iff_not_isIso`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_pullbackSection_dual_det_eq_zero_iff_not_isIso), where a determinant computed in such a basis detects failure of a map of modules to be an isomorphism at a point. The proof cites [`AlgebraicGeometry.Scheme.Modules.pullback_locally_mem_span_unit`](thm.html#AlgebraicGeometry.Scheme.Modules.pullback_locally_mem_span_unit), which provides local generation of the inverse image by pulled-back sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_basis_pullback_of_field_point.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_basis_pullback_of_field_point
    {X : Scheme.{u}} {M : X.Modules} {n : ℕ} {U : X.Opens} (e : Fin n → Γ(M, U))
    (he : ∀ (W : X.Opens) (hW : W ≤ U), ∃ b : Module.Basis (Fin n) Γ(X, W) Γ(M, W),
      ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i))
    {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ X)
    (hs : s.base (IsLocalRing.closedPoint K) ∈ U) :
    ∃ b : Module.Basis (Fin n) Γ(Spec (CommRingCat.of K), s ⁻¹ᵁ U)
        Γ((Scheme.Modules.pullback s).obj M, s ⁻¹ᵁ U),
      ∀ i, b i = ((Scheme.Modules.pullbackPushforwardAdjunction s).unit.app M).app U (e i) := by sorry
