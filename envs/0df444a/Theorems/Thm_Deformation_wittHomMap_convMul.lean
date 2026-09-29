-- Prove2me | Theorems.Thm_Deformation_wittHomMap_convMul
-- name    : Deformation.wittHomMap_convMul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/c90290a2-5e20-53dd-90ab-8c2909f285cb
-- title:
--   Additivity of Hom(-, Wₙ) under convolution of bialgebra maps
-- statement:
--   Let $R$ be a commutative ring, $p$ a prime and $n$ a natural number, let $A$ be a commutative ring carrying an $R$-bialgebra structure, and let $B$ be a commutative ring carrying an $R$-bialgebra structure whose comultiplication is cocommutative. Let $\varphi$ and $\psi$ be two $R$-bialgebra maps $B \to A$, regarded as elements of the type `WithConv` of such maps equipped with the convolution multiplication, and let $x$ be an element of [`Deformation.wittHom R p n B`](def/Dieudonne_WittVectorHom.html#L246), i.e. a length-$n$ truncated Witt vector over $B$ satisfying the homomorphism identity: the image of $x$ under the functorial map induced by the comultiplication $B \to B \otimes_R B$ equals the sum of its images under the maps induced by the two inclusions $B \to B \otimes_R B$ of the left and right factors. For a bialgebra map, [`Deformation.wittHomMap`](def/Dieudonne_WittVectorHom.html#L339) is the additive map between these subgroups obtained by applying the truncated Witt vector functor to the underlying ring map. The conclusion is that the map attached to the convolution product $\varphi * \psi$ sends $x$ to the sum of the images of $x$ under the maps attached to $\varphi$ and to $\psi$, as elements of [`Deformation.wittHom R p n A`](def/Dieudonne_WittVectorHom.html#L246).
--
--   In the language of affine group schemes, if $\varphi$ and $\psi$ correspond to homomorphisms $f, g \colon \operatorname{Spec} A \to \operatorname{Spec} B$ and $x$ to a homomorphism $\operatorname{Spec} B \to W_n$, this is the identity $x \circ (f+g) = x \circ f + x \circ g$, i.e. the additivity (in the source variable) of the functor $G \mapsto \operatorname{Hom}(G, W_n)$ underlying the Dieudonné module $\varinjlim_n \operatorname{Hom}(G, W_n)$. It is used in the construction of Honda systems attached to Cartier duals over a local ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_wittHomMap_convMul.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem Deformation.wittHomMap_convMul
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] {n : ℕ}
    {A : Type v} [CommRing A] [Bialgebra R A]
    {B : Type w} [CommRing B] [Bialgebra R B] [Coalgebra.IsCocomm R B]
    (φ ψ : WithConv (B →ₐc[R] A)) (x : Deformation.wittHom R p n B) :
    Deformation.wittHomMap p n (φ * ψ).ofConv x =
      Deformation.wittHomMap p n φ.ofConv x + Deformation.wittHomMap p n ψ.ofConv x := by sorry
