-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_basicOpen_quasicoherent_of_forall_exists_linearEquiv_tensorProduct
-- name    : AlgebraicGeometry.OModulePresheaf.forall_basicOpen_quasicoherent_of_forall_exists_linearEquiv_tensorProduct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/daa0680c-c50e-5e65-bd88-051a58799e77
-- title:
--   Base-changed module data are quasi-coherent on basic opens
-- statement:
--   Let $A$ be a commutative ring, let $q : P \to \operatorname{Spec} A$ be a morphism of schemes and let $p : V' \to P$ be a morphism of schemes. Let $F : \mathbb{N} \to$ `OModulePresheaf q` and $F' : \mathbb{N} \to$ `OModulePresheaf (p ≫ q)` be families of module data: for each index $k$ and each open $U$ one is given an abelian group $(F k)(U)$ carrying compatible $A$- and $\Gamma(P,U)$-module structures, together with $A$-linear restriction maps along inclusions that are semilinear for the restriction of sections and satisfy the identity and composition laws, and similarly for $F'$ over opens of $V'$ with its $A$- and $\Gamma(V',\cdot)$-actions. Suppose given, for every $k$, every affine open $U_0 \subseteq P$, every affine open $V \subseteq V'$ with $V \le p^{-1}U_0$, $A$-linear maps $\eta_{k,U_0,V} : (F k)(U_0) \to (F' k)(V)$ such that: $\eta(a \cdot x) = p^{\sharp}(a)\cdot\eta(x)$ for $a \in \Gamma(P,U_0)$, where $p^{\sharp}$ is `p.appLE`; the maps are compatible with restriction in $V$, i.e. restricting $\eta_{k,U_0,V_2}(x)$ to $V_1 \le V_2$ gives $\eta_{k,U_0,V_1}(x)$; and, regarding $\Gamma(V',V)$ as a $\Gamma(P,U_0)$-algebra via $p^{\sharp}$, there is a $\Gamma(V',V)$-linear isomorphism $\beta : \Gamma(V',V) \otimes_{\Gamma(P,U_0)} (F k)(U_0) \xrightarrow{\sim} (F' k)(V)$ with $\beta(1 \otimes x) = \eta_{k,U_0,V}(x)$. Then for every $k$, every affine open $U_0 \subseteq P$, every affine open $V \subseteq V'$ with $V \le p^{-1}U_0$ and every $f \in \Gamma(V',V)$ the two quasi-coherence clauses hold at $(V,f)$: every $x \in (F' k)(D(f))$ satisfies $f^{n}\cdot x = y|_{D(f)}$ for some $n$ and some $y \in (F' k)(V)$ (with $f^n$ restricted to $D(f)$), and every $y \in (F' k)(V)$ with $y|_{D(f)} = 0$ is annihilated by $f^{n}$ for some $n$.
--
--   This is the elementary form of the statement that a module datum obtained by base change along $p$ from module data on $P$ behaves on each small affine chart like the sheaf associated with a module: sections over a basic open $D(f)$ are a localisation at $f$ of the sections over the chart. It is used in the dévissage leading to [`AlgebraicGeometry.OModulePresheaf.exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper), where sections over arbitrary affine opens are threaded together after multiplication by suitable elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_forall_basicOpen_quasicoherent_of_forall_exists_linearEquiv_tensorProduct.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.OModulePresheaf.forall_basicOpen_quasicoherent_of_forall_exists_linearEquiv_tensorProduct
    {A : Type u} [CommRing A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))
    {V' : Scheme.{u}} (p : V' ⟶ P)
    (F : ℕ → OModulePresheaf q) (F' : ℕ → OModulePresheaf (p ≫ q))
    (η : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens), V.1 ≤ p ⁻¹ᵁ U₀.1 →
      ((F k).obj U₀.1 →ₗ[A] (F' k).obj V.1))
    (hηs : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U₀.1) (a : Γ(P, U₀.1))
      (x : (F k).obj U₀.1), η k U₀ V h (a • x) = (p.appLE U₀.1 V.1 h).hom a • η k U₀ V h x)
    (hηV : ∀ (k : ℕ) (U₀ : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ p ⁻¹ᵁ U₀.1)
      (h₂ : V₂.1 ≤ p ⁻¹ᵁ U₀.1) (hV : V₁.1 ≤ V₂.1) (x : (F k).obj U₀.1),
      (F' k).res hV (η k U₀ V₂ h₂ x) = η k U₀ V₁ h₁ x)
    (hβ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U₀.1),
      letI := (p.appLE U₀.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U₀.1)] (F k).obj U₀.1 ≃ₗ[Γ(V', V.1)] (F' k).obj V.1,
        ∀ x : (F k).obj U₀.1, β (1 ⊗ₜ x) = η k U₀ V h x)
    (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U₀.1) (f : Γ(V', V.1)) :
    (∀ x : (F' k).obj (V'.basicOpen f), ∃ (n : ℕ) (y : (F' k).obj V.1),
        (F' k).res (V'.basicOpen_le f) y = (V'.presheaf.map (homOfLE (V'.basicOpen_le f)).op).hom (f ^ n) • x) ∧
    (∀ y : (F' k).obj V.1, (F' k).res (V'.basicOpen_le f) y = 0 → ∃ n : ℕ, (f ^ n : Γ(V', V.1)) • y = 0) := by sorry
