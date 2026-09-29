-- Prove2me | Theorems.Thm_AlgebraicGeometry_appLE_surjective_of_isAffineOpen_preimage_of_isPullback_of_flat
-- name    : AlgebraicGeometry.appLE_surjective_of_isAffineOpen_preimage_of_isPullback_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/ce472cd7-6e29-5ae9-8232-43dfc33b7ef9
-- title:
--   Surjectivity of restriction along a flat π-adic thickening
-- statement:
--   Let $\mathcal O$ be a commutative ring which is a domain and let $\pi \in \mathcal O$ be irreducible. Let $(X_n)_{n \in \mathbb N}$ be a family of schemes equipped with morphisms $xb_n : X_n \to \operatorname{Spec}(\mathcal O/(\pi^{n+1}))$ and with transition morphisms $xt_n : X_n \to X_{n+1}$, and assume: (i) for every $n$ the square with sides $xt_n$, $xb_n$, $xb_{n+1}$ and the morphism $\operatorname{Spec}(\mathcal O/(\pi^{n+1})) \to \operatorname{Spec}(\mathcal O/(\pi^{n+2}))$ induced by the quotient map $\mathcal O/(\pi^{n+2}) \to \mathcal O/(\pi^{n+1})$ (coming from the inclusion of ideals $(\pi^{n+2}) \subseteq (\pi^{n+1})$) is cartesian, so that $X_n \cong X_{n+1} \times_{\operatorname{Spec}(\mathcal O/(\pi^{n+2}))} \operatorname{Spec}(\mathcal O/(\pi^{n+1}))$; (ii) each structure morphism $xb_n$ is flat. Fix $n \in \mathbb N$ and an open subscheme $U$ of $X_{n+1}$ such that the open $(xt_n)^{-1}(U)$ of $X_n$ is affine. The conclusion is that the ring map induced by $xt_n$ on sections, $\Gamma(U, \mathcal O_{X_{n+1}}) \to \Gamma((xt_n)^{-1}(U), \mathcal O_{X_n})$ (the `appLE` map associated with $U$, its preimage, and the identity inclusion), is surjective. No affineness is assumed of $U$ itself.
--
--   This is the lifting of sections along one step of a $\pi$-adic tower of thickenings: over an open whose trace on the reduction is affine, every function on the trace extends to the next level. It is used by [`AlgebraicGeometry.isAffineOpen_of_isAffineOpen_preimage_of_isPullback_of_flat`](thm.html#AlgebraicGeometry.isAffineOpen_of_isAffineOpen_preimage_of_isPullback_of_flat), which deduces that such an open $U$ is itself affine, the step needed to propagate affine opens up a flat tower of quotients of $\mathcal O$ by powers of $\pi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_appLE_surjective_of_isAffineOpen_preimage_of_isPullback_of_flat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.appLE_surjective_of_isAffineOpen_preimage_of_isPullback_of_flat
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (π : 𝒪) (hπ : Irreducible π)
    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (hflat : ∀ n : ℕ, Flat (xb n))
    (n : ℕ) (U : (X (n + 1)).Opens) (hU : IsAffineOpen ((xt n) ⁻¹ᵁ U)) :
    Function.Surjective ((xt n).appLE U ((xt n) ⁻¹ᵁ U) le_rfl) := by sorry
