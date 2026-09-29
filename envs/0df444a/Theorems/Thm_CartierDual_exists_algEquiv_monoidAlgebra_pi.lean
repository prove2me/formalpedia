-- Prove2me | Theorems.Thm_CartierDual_exists_algEquiv_monoidAlgebra_pi
-- name    : CartierDual.exists_algEquiv_monoidAlgebra_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/2238fa25-900d-5d3e-ad60-d77061bdad07
-- title:
--   Cartier dual of R[Γ] is Map(Γ,R)
-- statement:
--   Let $R$ be a commutative ring and $\Gamma$ a finite commutative group, and let $R[\Gamma]$ be the monoid algebra `MonoidAlgebra R Γ` with its standard bialgebra structure. Write $R[\Gamma]^{\vee}$ for [`CartierDual R (MonoidAlgebra R Γ)`](def/HopfAlgebra_CartierDual.html#L12), which by definition is the $R$-linear dual $\operatorname{Hom}_R(R[\Gamma],R)$ carried as a separate type, with [`CartierDual.toDual`](def/HopfAlgebra_CartierDual.html#L948) the identity $R$-linear equivalence onto that dual, and with the algebra, coalgebra and counit structures that the project attaches to it. The assertion is that there exists an $R$-algebra isomorphism $e : R[\Gamma]^{\vee} \xrightarrow{\sim} (\Gamma \to R)$ onto the $R$-algebra of $R$-valued functions on $\Gamma$ with pointwise operations, satisfying three compatibilities: first, $e(\varphi)(x) = \varphi(\mathrm{single}\,x\,1)$ for every $\varphi$ and every $x \in \Gamma$, i.e. $e$ is evaluation on the group-element basis; second, for all $\varphi$ and all $x,y \in \Gamma$, the comultiplication `Coalgebra.comul` of $\varphi$ in $R[\Gamma]^{\vee}$, transported by `toDual` on both tensor factors and paired with $\mathrm{single}\,x\,1 \otimes \mathrm{single}\,y\,1$ via `TensorProduct.dualDistrib`, equals $\varphi(\mathrm{single}\,(xy)\,1)$; third, `Coalgebra.counit` $\varphi = \varphi(1)$ for every $\varphi$.
--
--   This is the evaluation dictionary identifying the Cartier dual of the diagonalisable group scheme $\operatorname{Spec} R[\Gamma]$ with the constant group scheme $\Gamma$: the convolution product on the dual becomes the pointwise product of functions, the comultiplication of the dual is the transpose of $[x][y] = [xy]$, hence dual to the group law of $\Gamma$, and the counit is evaluation at the identity. It is used in the project's Cartier-duality package, for instance by the results on points of Hopf algebras with local Cartier dual and inertia conditions, and in the construction of block idempotents from a quotient with trivial inertia.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CartierDual_exists_algEquiv_monoidAlgebra_pi.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CartierDual.exists_algEquiv_monoidAlgebra_pi
    (R : Type*) [CommRing R] (Γ : Type*) [CommGroup Γ] [Fintype Γ] :
    ∃ e : CartierDual R (MonoidAlgebra R Γ) ≃ₐ[R] (Γ → R),
      (∀ (φ : CartierDual R (MonoidAlgebra R Γ)) (x : Γ), e φ x = φ (MonoidAlgebra.single x 1)) ∧
      (∀ (φ : CartierDual R (MonoidAlgebra R Γ)) (x y : Γ),
        TensorProduct.dualDistrib R (MonoidAlgebra R Γ) (MonoidAlgebra R Γ)
          (TensorProduct.map (CartierDual.toDual R (MonoidAlgebra R Γ)).toLinearMap
            (CartierDual.toDual R (MonoidAlgebra R Γ)).toLinearMap (Coalgebra.comul (R := R) φ))
          (MonoidAlgebra.single x 1 ⊗ₜ[R] MonoidAlgebra.single y 1) = φ (MonoidAlgebra.single (x * y) 1)) ∧
      (∀ φ : CartierDual R (MonoidAlgebra R Γ), Coalgebra.counit (R := R) φ = φ 1) := by sorry
