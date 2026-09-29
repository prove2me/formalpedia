-- Prove2me | Theorems.Thm_CartierDual_exists_algHomEquiv_groupLike
-- name    : CartierDual.exists_algHomEquiv_groupLike
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/904cdd18-8c23-5004-9410-fed00f016d4c
-- title:
--   Cartier dual corepresents group-like elements
-- statement:
--   Let $R$ be a commutative ring and $H$ a commutative ring equipped with an $R$-bialgebra structure which is finite and free as an $R$-module; recall that [`CartierDual R H`](def/HopfAlgebra_CartierDual.html#L12) is by definition the $R$-linear dual $\operatorname{Hom}_R(H,R)$ (with its $R$-algebra structure), and [`CartierDual.toDual`](def/HopfAlgebra_CartierDual.html#L948) is the identity identification of it with that dual. The assertion is that there exists a family $e$ which, for every commutative $R$-algebra $B$ (in a fixed universe), gives a bijection between the $R$-algebra homomorphisms $\psi\colon \mathrm{CartierDual}\,R\,H \to B$ and the group-like elements of the $B$-coalgebra $B \otimes_R H$, subject to four compatibilities: (i) for every $\psi$ and every $\varphi \in \mathrm{CartierDual}\,R\,H$, contracting the underlying element of $e_B(\psi)$ against $\varphi$ in the second factor, i.e. applying $\mathrm{id}_B \otimes \varphi$ followed by the identification $B \otimes_R R \cong B$, returns $\psi(\varphi)$; (ii) if $\psi_0$ satisfies $\psi_0(\varphi) = \varphi(1)$ in $B$ for all $\varphi$, then $e_B(\psi_0)$ has underlying element $1$; (iii) if the convolution products satisfy $\psi_3 = \psi_1 * \psi_2$ as elements of `WithConv`, then the underlying element of $e_B(\psi_3)$ is the product of those of $e_B(\psi_1)$ and $e_B(\psi_2)$; (iv) for an $R$-algebra map $\tau\colon B \to B'$, the underlying element of $e_{B'}(\tau \circ \psi)$ is the image of that of $e_B(\psi)$ under $\tau \otimes \mathrm{id}_H$.
--
--   This is the corepresentability statement of Cartier duality in algebra form: the $B$-points of the Cartier dual of $H$ are the characters of $H$, i.e. the group-like elements of $B \otimes_R H$, with the unit, convolution and base-change compatibilities recorded explicitly. It is used in the study of finite flat group schemes, in particular by the results producing surjective bialgebra maps from monoid algebras onto Hopf algebras of multiplicative type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CartierDual_exists_algHomEquiv_groupLike.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem CartierDual.exists_algHomEquiv_groupLike
    (R : Type u) [CommRing R] (H : Type v) [CommRing H] [Bialgebra R H] [Module.Finite R H] [Module.Free R H] :
    ∃ e : (∀ (B : Type w) [CommRing B] [Algebra R B], (CartierDual R H →ₐ[R] B) ≃ GroupLike B (TensorProduct R B H)),
      (∀ (B : Type w) [CommRing B] [Algebra R B] (ψ : CartierDual R H →ₐ[R] B) (φ : CartierDual R H),
          TensorProduct.rid R B (LinearMap.lTensor B (CartierDual.toDual R H φ) (e B ψ).val) = ψ φ) ∧
      (∀ (B : Type w) [CommRing B] [Algebra R B] (ψ₀ : CartierDual R H →ₐ[R] B),
          (∀ φ, ψ₀ φ = algebraMap R B (φ 1)) → (e B ψ₀).val = 1) ∧
      (∀ (B : Type w) [CommRing B] [Algebra R B] (ψ₁ ψ₂ ψ₃ : CartierDual R H →ₐ[R] B),
          WithConv.toConv ψ₃.toLinearMap = WithConv.toConv ψ₁.toLinearMap * WithConv.toConv ψ₂.toLinearMap →
          (e B ψ₃).val = (e B ψ₁).val * (e B ψ₂).val) ∧
      (∀ (B B' : Type w) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] (τ : B →ₐ[R] B')
          (ψ : CartierDual R H →ₐ[R] B),
          (e B' (τ.comp ψ)).val = Algebra.TensorProduct.map τ (AlgHom.id R H) (e B ψ).val) := by sorry
