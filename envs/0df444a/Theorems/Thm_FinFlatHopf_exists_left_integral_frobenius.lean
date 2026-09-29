-- Prove2me | Theorems.Thm_FinFlatHopf_exists_left_integral_frobenius
-- name    : FinFlatHopf.exists_left_integral_frobenius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/5d9f8311-12c2-56e2-a444-b873aa1797b4
-- title:
--   Left integral and Frobenius map over a local base
-- statement:
--   Let $B$ be a commutative local ring and let $H$ be a commutative ring carrying the structure of a Hopf algebra over $B$ which, as a $B$-module, is free and of finite type. The assertion is the existence of an element $l$ of `WithConv (H →ₗ[B] B)`, that is, of the $B$-linear dual of $H$ equipped with the convolution product, with two properties. First, $l$ is a left integral for convolution: for every $f$ in the convolution algebra on the dual, $f * l = f(1)\,l$, the scalar being the value of $f$ at the identity element $1$ of $H$ and the product being the convolution product. Second, the antipode-twisted Frobenius map is bijective as a map of underlying sets: sending $h \in H$ to the element of the convolution algebra whose underlying linear functional is $x \mapsto l(x \cdot S(h))$, where $S$ denotes the antipode of $H$ over $B$, gives a bijection from $H$ onto `WithConv (H →ₗ[B] B)`. No assumption is made on the rank of $H$, on the residue characteristic of $B$, or on cocommutativity.
--
--   This is the Larson–Sweedler theorem — a finite free Hopf algebra is a Frobenius algebra, with space of left integrals on the dual free of rank one — in the case of a local base ring, where finitely generated projective modules are free; bijectivity of the twisted Frobenius map expresses that the dual is free of rank one over $H$ as a Hopf module. It is used in [`FinFlatHopf.not_isLocalRing_dual_of_isLocalRing`](thm.html#FinFlatHopf.not_isLocalRing_dual_of_isLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FinFlatHopf_exists_left_integral_frobenius.lean

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Finiteness.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FinFlatHopf.exists_left_integral_frobenius
    (B : Type) [CommRing B] [IsLocalRing B]
    (H : Type) [CommRing H] [HopfAlgebra B H] [Module.Free B H] [Module.Finite B H] :
    ∃ l : WithConv (H →ₗ[B] B),
      (∀ f : WithConv (H →ₗ[B] B), f * l = f 1 • l) ∧
      Function.Bijective (fun h : H =>
        WithConv.toConv (l.ofConv ∘ₗ LinearMap.mulRight B (HopfAlgebra.antipode B h))) := by sorry
