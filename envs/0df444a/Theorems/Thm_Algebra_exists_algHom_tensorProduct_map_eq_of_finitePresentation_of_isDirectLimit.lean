-- Prove2me | Theorems.Thm_Algebra_exists_algHom_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit
-- name    : Algebra.exists_algHom_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/3315dbcb-4dbc-5173-b2c3-eb0b644875c8
-- title:
--   Algebra maps between base changes descend to a finite stage
-- statement:
--   Let $\iota$ be a non-empty directed preordered index type, let $R_0$ be a commutative ring, let $G$ be a family of commutative $R_0$-algebras indexed by $\iota$, and let $f_{ij} \colon G_i \to G_j$, for $i \le j$, be $R_0$-algebra homomorphisms forming a directed system (the underlying maps are compatible with composition and identities). Let $R$ be a commutative $R_0$-algebra which is also a $G_i$-algebra for every $i$, compatibly with the $R_0$-structures via scalar towers, and assume the hypothesis [`IsDirectLimit`](def/Mathlib_Algebra_IsDirectLimit.html#L8) for the system $(f_{ij})$ together with the structure maps $\mathrm{algebraMap} \colon G_i \to R$: every element of $R$ is the image of some element of some $G_i$; whenever $m_i \in G_i$ and $m_j \in G_j$ have the same image in $R$, there is $k$ with $i \le k$, $j \le k$ and $f_{ik}(m_i) = f_{jk}(m_j)$; and the structure maps are compatible, $\mathrm{algebraMap}(f_{ij}(x)) = \mathrm{algebraMap}(x)$. Let $A$ be a commutative $R_0$-algebra of finite presentation over $R_0$, let $B$ be an arbitrary commutative $R_0$-algebra, and let $\varphi \colon R \otimes_{R_0} A \to R \otimes_{R_0} B$ be a homomorphism of $R$-algebras. Then there exist an index $i$ and a homomorphism of $G_i$-algebras $\varphi_0 \colon G_i \otimes_{R_0} A \to G_i \otimes_{R_0} B$ such that for every $x \in G_i \otimes_{R_0} A$ the image of $\varphi_0(x)$ under $\mathrm{algebraMap}(G_i \to R) \otimes \mathrm{id}_B$ equals $\varphi$ applied to the image of $x$ under $\mathrm{algebraMap}(G_i \to R) \otimes \mathrm{id}_A$; that is, $\varphi$ is the base change of $\varphi_0$ along $G_i \to R$, the commutativity being stated pointwise.
--
--   This is the surjectivity half of the standard statement that morphisms between base changes of a finitely presented algebra to a filtered colimit of rings come from a finite stage (EGA IV, 8.8.2). It is used by [`Algebra.exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit`](thm.html#Algebra.exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit), which upgrades the descended homomorphism to an isomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_algHom_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit.lean

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u₀ u v w w₁ w₂

theorem Algebra.exists_algHom_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R₀ : Type u₀) [CommRing R₀]
    (G : ι → Type v) [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
    (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j) [DirectedSystem G fun i j h => ⇑(f i j h)]
    (R : Type w) [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R] [∀ i, IsScalarTower R₀ (G i) R]
    (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
    (A : Type w₁) [CommRing A] [Algebra R₀ A] [Algebra.FinitePresentation R₀ A]
    (B : Type w₂) [CommRing B] [Algebra R₀ B]
    (φ : R ⊗[R₀] A →ₐ[R] R ⊗[R₀] B) :
    ∃ (i : ι) (φ₀ : G i ⊗[R₀] A →ₐ[G i] G i ⊗[R₀] B),
      ∀ x : G i ⊗[R₀] A,
        φ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ A) x) =
          Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ B) (φ₀ x) := by sorry
