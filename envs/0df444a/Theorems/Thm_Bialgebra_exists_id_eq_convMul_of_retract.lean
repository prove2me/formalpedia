-- Prove2me | Theorems.Thm_Bialgebra_exists_id_eq_convMul_of_retract
-- name    : Bialgebra.exists_id_eq_convMul_of_retract
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/8d833c7c-9256-5d55-a52f-8c426c3b3054
-- title:
--   Transporting an Fa * bV convolution identity to a bialgebra retract
-- statement:
--   Let $k$ be a commutative ring and let $D$, $X$ be commutative $k$-bialgebras whose comultiplications are cocommutative. Assume given bialgebra homomorphisms $r \colon D \to X$ and $j \colon X \to D$ with $r \circ j = \mathrm{id}_X$; a $k$-linear endomorphism $e$ of $D$ with $r \circ e \circ j = \mathrm{id}_X$; algebra endomorphisms $F_D$ of $D$ and $F_X$ of $X$ with $r \circ F_D = F_X \circ r$; coalgebra endomorphisms $V_D$ of $D$ and $V_X$ of $X$ with $V_D \circ j = j \circ V_X$; and bialgebra endomorphisms $a, b$ of $D$ such that, in the convolution monoid structure on $k$-linear endomorphisms (the `WithConv` multiplication, i.e. $u * v = \mu \circ (u \otimes v) \circ \Delta$), one has $e = (F_D \circ a) * (b \circ V_D)$. The conclusion asserts the existence of bialgebra endomorphisms $a'$, $b'$ of $X$ that are equal to $r \circ a \circ j$ and $r \circ b \circ j$ respectively and satisfy $\mathrm{id}_X = (F_X \circ a') * (b' \circ V_X)$ in the same convolution product; the witnesses are exactly those two composites, so the statement is the identity for $a' = r \circ a \circ j$, $b' = r \circ b \circ j$ packaged existentially.
--
--   This is the transport of a Frobenius–Verschiebung convolution identity along a retraction of bialgebras: a decomposition $e = (F_D a) * (b V_D)$ of a linear endomorphism of $D$ that restricts to the identity on the retract $X$ becomes such a decomposition of $\mathrm{id}_X$ with the conjugated endomorphisms. It is used in the construction of a split idempotent decomposition of a Hopf algebra, where the Frobenius–Verschiebung hypothesis must be passed from a Cartier dual to the dual of the image of an idempotent and then to a local factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Bialgebra_exists_id_eq_convMul_of_retract.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem Bialgebra.exists_id_eq_convMul_of_retract
    {k : Type u} [CommRing k] {D : Type v} [CommRing D] [Bialgebra k D] [Coalgebra.IsCocomm k D]
    {X : Type v} [CommRing X] [Bialgebra k X] [Coalgebra.IsCocomm k X]
    (r : D →ₐc[k] X) (j : X →ₐc[k] D) (hrj : r.comp j = BialgHom.id k X)
    (e : D →ₗ[k] D) (hrej : (r : D →ₗ[k] X) ∘ₗ e ∘ₗ (j : X →ₗ[k] D) = LinearMap.id)
    (FD : D →ₐ[k] D) (FX : X →ₐ[k] X) (hF : (r : D →ₐ[k] X).comp FD = FX.comp (r : D →ₐ[k] X))
    (VD : D →ₗc[k] D) (VX : X →ₗc[k] X) (hV : (VD : D →ₗ[k] D) ∘ₗ (j : X →ₗ[k] D) = (j : X →ₗ[k] D) ∘ₗ (VX : X →ₗ[k] X))
    (a b : D →ₐc[k] D)
    (he : e = (WithConv.toConv (FD.toLinearMap ∘ₗ (a : D →ₗ[k] D)) *
        WithConv.toConv ((b : D →ₗ[k] D) ∘ₗ (VD : D →ₗ[k] D))).ofConv) :
    ∃ a' b' : X →ₐc[k] X,
      a' = (r.comp a).comp j ∧ b' = (r.comp b).comp j ∧
      (LinearMap.id : X →ₗ[k] X) =
        (WithConv.toConv (FX.toLinearMap ∘ₗ (a' : X →ₗ[k] X)) *
          WithConv.toConv ((b' : X →ₗ[k] X) ∘ₗ (VX : X →ₗ[k] X))).ofConv := by sorry
