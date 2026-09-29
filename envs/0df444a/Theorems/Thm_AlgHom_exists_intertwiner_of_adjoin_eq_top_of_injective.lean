-- Prove2me | Theorems.Thm_AlgHom_exists_intertwiner_of_adjoin_eq_top_of_injective
-- name    : AlgHom.exists_intertwiner_of_adjoin_eq_top_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/149a9554-064c-5ccf-8528-7bd0b5719df9
-- title:
--   Intertwining R-algebra map from generators, via faithful action
-- statement:
--   Let $R$ be a commutative ring, let $C_1$ and $C_0$ be commutative $R$-algebras, and let $M_1$, $M_0$ be abelian groups carrying compatible $R$-module and $C_1$- respectively $C_0$-module structures (scalar-tower hypotheses relating $R$ to $C_1$ on $M_1$ and to $C_0$ on $M_0$). Let $i \colon M_0 \to M_1$ be an injective $R$-linear map, and assume $C_0$ acts faithfully on $M_0$, i.e. any $y \in C_0$ with $y \cdot m = 0$ for all $m \in M_0$ is zero. Let $G \subseteq C_1$ be a set generating $C_1$ as an $R$-algebra, $\mathrm{adjoin}_R G = \top$, and let $y \colon C_1 \to C_0$ be an arbitrary function whose values on $G$ are intertwining partners: $g \cdot i(m) = i(y(g) \cdot m)$ for all $g \in G$ and all $m \in M_0$. The conclusion asserts the existence of an $R$-algebra homomorphism $\mathrm{res} \colon C_1 \to C_0$ such that (i) $t \cdot i(m) = i(\mathrm{res}(t) \cdot m)$ for all $t \in C_1$ and $m \in M_0$; (ii) $\mathrm{res}(g) = y(g)$ for every $g \in G$; and (iii) every $R$-algebra homomorphism $C_1 \to C_0$ with the intertwining property (i) equals $\mathrm{res}$. Note that $y$ is only constrained on $G$, and no hypothesis is placed on the $C_1$-module $M_1$ beyond the stated compatibilities.
--
--   This is the elementary transfer mechanism behind Wiles's homomorphism between localised Hecke algebras defined through an $\alpha$-stabilised degeneracy map: Hecke operators generating the algebra at the higher level intertwine with prescribed operators on the lower-level space, whence a unique algebra homomorphism sending $U_p$ to the unit root $\alpha$. It is used in the construction of the algebra homomorphism on corner rings attached to degeneracy maps in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgHom_exists_intertwiner_of_adjoin_eq_top_of_injective.lean

import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Algebra.Algebra.Tower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgHom.exists_intertwiner_of_adjoin_eq_top_of_injective
    {R : Type} [CommRing R]
    {C₁ C₀ : Type} [CommRing C₁] [CommRing C₀] [Algebra R C₁] [Algebra R C₀]
    {M₁ M₀ : Type} [AddCommGroup M₁] [AddCommGroup M₀] [Module R M₁] [Module R M₀]
    [Module C₁ M₁] [Module C₀ M₀] [IsScalarTower R C₁ M₁] [IsScalarTower R C₀ M₀]
    (i : M₀ →ₗ[R] M₁) (hi : Function.Injective i)
    (hfaith : ∀ y : C₀, (∀ m : M₀, y • m = 0) → y = 0)
    (G : Set C₁) (hG : Algebra.adjoin R G = ⊤)
    (y : C₁ → C₀) (hy : ∀ g ∈ G, ∀ m : M₀, g • i m = i (y g • m)) :
    ∃ res : C₁ →ₐ[R] C₀,
      (∀ (t : C₁) (m : M₀), t • i m = i (res t • m)) ∧
      (∀ g ∈ G, res g = y g) ∧
      (∀ res' : C₁ →ₐ[R] C₀, (∀ (t : C₁) (m : M₀), t • i m = i (res' t • m)) → res' = res) := by sorry
