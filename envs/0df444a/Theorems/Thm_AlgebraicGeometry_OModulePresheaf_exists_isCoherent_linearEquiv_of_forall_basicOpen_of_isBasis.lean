-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis
-- name    : AlgebraicGeometry.OModulePresheaf.exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/87da6325-265e-50b1-a811-f82c46bd4cda
-- title:
--   Gluing coherent module data from a basis of affine opens
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme and $\pi : V \to \operatorname{Spec} R$ a morphism. Let $B$ be a set of affine opens of $V$ that is downward closed (if $W' \le W$ as affine opens and $W \in B$ then $W' \in B$) and covers $V$ (every point of $V$ lies in some member of $B$). Suppose given, for each $W \in B$, a type $M(W)$ carrying an abelian group structure, an $R$-module structure and a $\Gamma(V,W)$-module structure, compatible through the $R$-algebra structure on $\Gamma(V,W)$ induced by $\pi$; restriction maps $\operatorname{res}_h : M(W) \to M(W')$, $R$-linear, for each inclusion $h : W' \le W$ of members of $B$, semilinear over the presheaf restriction $\Gamma(V,W) \to \Gamma(V,W')$, equal to the identity for $h = \mathrm{id}$ and compatible with composition; the localisation condition on basic opens: for $W, W_g \in B$, $g \in \Gamma(V,W)$ with $W_g = V.\mathrm{basicOpen}\,g$, every $y \in M(W_g)$ satisfies $\operatorname{res}(x) = g^n\cdot y$ for some $n$ and some $x \in M(W)$ (with $g^n$ restricted to $W_g$), and every $x \in M(W)$ restricting to $0$ on $W_g$ is killed by some $g^n$; and finiteness: each $M(W)$ is a finite $\Gamma(V,W)$-module. Then there exist an `OModulePresheaf` $G$ for $\pi$ — modules $G(U)$ for all opens $U$ of $V$, each an $R$-module and a $\Gamma(V,U)$-module compatibly, with $R$-linear functorial semilinear restrictions — and $R$-linear isomorphisms $e_W : G(W) \simeq M(W)$ for $W \in B$ such that: $G(U)$ is a finite $\Gamma(V,U)$-module for every affine open $U$; $G$ satisfies the same localisation condition on basic opens of all affine opens; each $e_W$ is $\Gamma(V,W)$-linear and commutes with the restrictions; and $G$ has both universal properties on affine opens: for every quasi-coherent $F$ and every family of $R$-linear maps $\theta_W : M(W) \to F(W)$ ($W \in B$) that is $\Gamma(V,W)$-linear and compatible with restrictions there is exactly one `AffHom` $\Phi : G \to F$ (a family of $\Gamma$-linear maps on all affine opens commuting with restrictions) with $\Phi_W = \theta_W \circ e_W$, and symmetrically, for every such family $\vartheta_W : F(W) \to M(W)$ there is exactly one `AffHom` $\Psi : F \to G$ with $e_W \circ \Psi_W = \vartheta_W$.
--
--   This is Grothendieck's construction of a (quasi-)coherent module from data given only on a basis of affine opens stable under shrinking, together with the resulting bijections between morphisms on affine opens and morphisms of the basis data. It is used in the extension step of the Grothendieck existence argument for proper morphisms over adically complete rings and in the construction of coherent quotient/extension data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R))

    (B : Set V.affineOpens)
    (hdown : ∀ (W W' : V.affineOpens), W'.1 ≤ W.1 → W ∈ B → W' ∈ B)
    (hcov : ∀ x : V, ∃ W ∈ B, x ∈ W.1)

    (M : ↥B → Type u) [∀ W, AddCommGroup (M W)] [∀ W, Module R (M W)] [∀ W, Module Γ(V, W.1.1) (M W)]
    [∀ W : ↥B, letI := Scheme.TwoAffineOpenCover.algebraOfHom π W.1.1; IsScalarTower R Γ(V, W.1.1) (M W)]
    (res : ∀ {W W' : ↥B}, W'.1.1 ≤ W.1.1 → (M W →ₗ[R] M W'))
    (res_smul : ∀ {W W' : ↥B} (h : W'.1.1 ≤ W.1.1) (a : Γ(V, W.1.1)) (x : M W),
      res h (a • x) = (V.presheaf.map (homOfLE h).op).hom a • res h x)
    (res_refl : ∀ (W : ↥B) (x : M W), res (le_refl W.1.1) x = x)
    (res_comp : ∀ {W W' W'' : ↥B} (h : W''.1.1 ≤ W'.1.1) (h' : W'.1.1 ≤ W.1.1) (x : M W),
      res (h.trans h') x = res h (res h' x))
    (hqc : ∀ (W Wg : ↥B) (g : Γ(V, W.1.1)) (hWg : Wg.1.1 = V.basicOpen g),
      (∀ y : M Wg, ∃ (n : ℕ) (x : M W),
          res (hWg.trans_le (V.basicOpen_le g)) x =
            (V.presheaf.map (homOfLE (hWg.trans_le (V.basicOpen_le g))).op).hom (g ^ n) • y) ∧
      (∀ x : M W, res (hWg.trans_le (V.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
    (hfg : ∀ W : ↥B, Module.Finite (Γ(V, W.1.1) : Type u) (M W)) :
    ∃ (G : OModulePresheaf π) (e : ∀ W : ↥B, G.obj W.1.1 ≃ₗ[R] M W),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (W : ↥B) (a : Γ(V, W.1.1)) (x : G.obj W.1.1), e W (a • x) = a • e W x) ∧
      (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : G.obj W.1.1), e W' (G.res h x) = res h (e W x)) ∧

      (∀ (F : OModulePresheaf π), F.IsQuasicoherent →
        ∀ (θ : ∀ W : ↥B, M W →ₗ[R] F.obj W.1.1),
          (∀ (W : ↥B) (a : Γ(V, W.1.1)) (x : M W), θ W (a • x) = a • θ W x) →
          (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : M W), θ W' (res h x) = F.res h (θ W x)) →
          ∃! Φ : OModulePresheaf.AffHom G F, ∀ (W : ↥B) (x : G.obj W.1.1), Φ.app W.1 x = θ W (e W x)) ∧

      (∀ (F : OModulePresheaf π), F.IsQuasicoherent →
        ∀ (ϑ : ∀ W : ↥B, F.obj W.1.1 →ₗ[R] M W),
          (∀ (W : ↥B) (a : Γ(V, W.1.1)) (x : F.obj W.1.1), ϑ W (a • x) = a • ϑ W x) →
          (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : F.obj W.1.1), ϑ W' (F.res h x) = res h (ϑ W x)) →
          ∃! Ψ : OModulePresheaf.AffHom F G, ∀ (W : ↥B) (x : F.obj W.1.1), e W (Ψ.app W.1 x) = ϑ W x) := by sorry
