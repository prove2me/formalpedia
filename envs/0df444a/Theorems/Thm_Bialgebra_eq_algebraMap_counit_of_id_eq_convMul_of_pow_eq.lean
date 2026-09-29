-- Prove2me | Theorems.Thm_Bialgebra_eq_algebraMap_counit_of_id_eq_convMul_of_pow_eq
-- name    : Bialgebra.eq_algebraMap_counit_of_id_eq_convMul_of_pow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/7fd9bbbb-2867-5eae-9958-5d1c96d6cb71
-- title:
--   Triviality of a bialgebra with id=(F∘ a)*(b∘ V)
-- statement:
--   Let $k$ be a commutative ring and let $X$ be a commutative ring equipped with a $k$-bialgebra structure. Let $F \colon X \to X$ be a $k$-algebra endomorphism, $V \colon X \to X$ a $k$-coalgebra endomorphism, $a, b \colon X \to X$ two endomorphisms that are simultaneously algebra and coalgebra maps over $k$, and $m$ a natural number. Assume that $F$ commutes with $a$ and with $b$ as algebra endomorphisms, that the $m$-th power of $F$ as a $k$-linear endomorphism sends each $x$ to $\eta(\varepsilon(x)) = \mathrm{algebraMap}\,k\,X(\varepsilon(x))$, that the $m$-th power of the underlying linear map of $V$ does the same, and that the identity map of $X$ equals, in the convolution monoid structure on $\mathrm{End}_k(X)$ (the multiplication transported through `WithConv.toConv`/`ofConv`), the convolution product of $F \circ a$ with $b \circ V$, in that order. The conclusion is that $x = \eta(\varepsilon(x))$ for every $x \in X$, i.e. the identity of $X$ coincides with $\eta \circ \varepsilon$, so $\operatorname{Spec} X$ is the trivial group scheme.
--
--   This is the elementary algebraic core of the assertion that an endomorphism of a finite commutative group scheme which factors through both Frobenius and Verschiebung kills the local-local part: the convolution identity $\mathrm{id} = (F\circ a)*(b\circ V)$ together with $F^m = V^m = \eta\circ\varepsilon$ forces the bialgebra to be trivial. It is used in the splitting theorem [`HopfAlgebra.exists_split_idempotent_bijective_tensorProduct_isReduced_cartierDual_of_cartierDualMap_eq_frobenius_conv_verschiebung`](thm.html#HopfAlgebra.exists_split_idempotent_bijective_tensorProduct_isReduced_cartierDual_of_cartierDualMap_eq_frobenius_conv_verschiebung), where the local-local factor is shown to vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Bialgebra_eq_algebraMap_counit_of_id_eq_convMul_of_pow_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem Bialgebra.eq_algebraMap_counit_of_id_eq_convMul_of_pow_eq
    {k : Type u} [CommRing k] {X : Type v} [CommRing X] [Bialgebra k X]
    (F : X →ₐ[k] X) (V : X →ₗc[k] X) (a b : X →ₐc[k] X) (m : ℕ)
    (hFa : F.comp (a : X →ₐ[k] X) = (a : X →ₐ[k] X).comp F)
    (hFb : F.comp (b : X →ₐ[k] X) = (b : X →ₐ[k] X).comp F)
    (hFm : ∀ x, (F.toLinearMap ^ m) x = algebraMap k X (Coalgebra.counit (R := k) x))
    (hVm : ∀ x, ((V : X →ₗ[k] X) ^ m) x = algebraMap k X (Coalgebra.counit (R := k) x))
    (hid : (LinearMap.id : X →ₗ[k] X) =
      (WithConv.toConv (F.toLinearMap ∘ₗ (a : X →ₗ[k] X)) *
        WithConv.toConv ((b : X →ₗ[k] X) ∘ₗ (V : X →ₗ[k] X))).ofConv) :
    ∀ x : X, x = algebraMap k X (Coalgebra.counit (R := k) x) := by sorry
