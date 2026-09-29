-- Prove2me | Theorems.Thm_CartierDual_dualBaseChangeLin_bijective_integral
-- name    : CartierDual.dualBaseChangeLin_bijective_integral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/d5e41585-6479-57fd-8614-fd4720222109
-- title:
--   Cartier duality commutes with base change: finite free case
-- statement:
--   Let $O$ be a commutative ring, $O'$ a commutative $O$-algebra, and $A$ a commutative Hopf algebra over $O$ which is finite and free as an $O$-module. Write $\mathrm{CartierDual}\,O\,A$ for the $O$-linear dual $\operatorname{Hom}_O(A,O)$, and let $\beta =$ [`CartierDual.dualBaseChangeLin O O' A`](def/HopfAlgebra_CharacterClosure.html#L151) be the $O'$-linear map $O' \otimes_O \operatorname{Hom}_O(A,O) \to \operatorname{Hom}_{O'}(O' \otimes_O A, O')$ obtained by base change from $\varphi \mapsto (c \otimes a \mapsto c\,\varphi(a))$, so that $\beta(c \otimes \varphi)$ sends $c' \otimes a$ to $c c' \varphi(a)$. The assertion is a fivefold conjunction: $\beta$ is bijective; $\beta(1) = 1$; $\beta(xy) = \beta(x)\beta(y)$ for all $x, y \in O' \otimes_O \operatorname{Hom}_O(A,O)$; for every $w$ in that tensor product, $(\beta \otimes \beta)(\Delta w) = \Delta(\beta w)$, where $\Delta$ denotes the comultiplication over $O'$ on source and target respectively; and for every $g \in \operatorname{Hom}_O(A,O)$ and every $x \in O' \otimes_O A$, $\beta(1 \otimes S g)(x) = \beta(1 \otimes g)(S' x)$, where $S$ is the antipode over $O$ of the dual and $S'$ the antipode over $O'$ of $O' \otimes_O A$. All multiplications, units, comultiplications and antipodes are those carried by the respective types.
--
--   This is the statement that Cartier duality commutes with arbitrary base change, in the case of a Hopf algebra that is finite and free over the base ring, with no field or Noetherian hypothesis on $O \to O'$; the conclusion records bijectivity together with compatibility with unit, product, comultiplication and antipode, so that the base-change map is an isomorphism of Hopf algebras. It is used in the analysis of Cartier duals after base change to local rings, in particular in the results identifying points and local structure of the dual, which feed into the treatment of finite flat group schemes of multiplicative type in the Galois-representation part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CartierDual_dualBaseChangeLin_bijective_integral.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CharacterClosure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem CartierDual.dualBaseChangeLin_bijective_integral.{u, v, w}
    (O : Type u) [CommRing O] (O' : Type v) [CommRing O'] [Algebra O O']
    (A : Type w) [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A] :
    Function.Bijective (CartierDual.dualBaseChangeLin O O' A) ∧
    CartierDual.dualBaseChangeLin O O' A 1 = 1 ∧
    (∀ x y : O' ⊗[O] CartierDual O A,
        CartierDual.dualBaseChangeLin O O' A (x * y)
          = CartierDual.dualBaseChangeLin O O' A x * CartierDual.dualBaseChangeLin O O' A y) ∧
    (∀ w : O' ⊗[O] CartierDual O A,
        TensorProduct.map (CartierDual.dualBaseChangeLin O O' A) (CartierDual.dualBaseChangeLin O O' A)
            (Coalgebra.comul (R := O') w)
          = Coalgebra.comul (R := O') (CartierDual.dualBaseChangeLin O O' A w)) ∧
    (∀ (g : CartierDual O A) (x : O' ⊗[O] A),
        CartierDual.dualBaseChangeLin O O' A ((1 : O') ⊗ₜ[O] HopfAlgebraStruct.antipode (R := O) g) x
          = CartierDual.dualBaseChangeLin O O' A ((1 : O') ⊗ₜ[O] g) (HopfAlgebraStruct.antipode (R := O') x)) := by sorry
