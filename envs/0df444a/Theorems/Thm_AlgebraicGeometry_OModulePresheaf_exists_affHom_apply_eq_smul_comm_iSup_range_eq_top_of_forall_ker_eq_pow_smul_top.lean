-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top
-- name    : AlgebraicGeometry.OModulePresheaf.exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/7b001cba-5e10-5605-87cb-5221e493f604
-- title:
--   Multiplication by generators of I on the graded pieces
-- statement:
--   Let $A$ be a commutative ring, $I\subseteq A$ an ideal, and $g:\{0,\dots,s-1\}\to A$ a finite family whose span is $I$. Let $V$ be a scheme with a morphism $\pi:V\to\operatorname{Spec}A$. Throughout, an `OModulePresheaf` for $\pi$ is the data, for each open $U\subseteq V$, of an abelian group that is simultaneously an $A$-module and a $\Gamma(V,U)$-module, compatibly via the algebra structure induced by $\pi$, together with $A$-linear restriction maps for $U\le U'$ that are semilinear for restriction of sections and satisfy the identity and composition laws; an `AffHom` between two such is a family of $A$-linear maps on affine opens only, semilinear for the $\Gamma(V,U)$-action and commuting with restriction along inclusions of affine opens. Given $F:\mathbb N\to$ such presheaves and transition maps $\varphi_k:F(k+1)\to F(k)$ which on every affine open $U$ are surjective with kernel $I^{k+1}\cdot\top$ inside $F(k+1)(U)$, and given $K:\mathbb N\to$ such presheaves with maps $j_k:K(k)\to F(k+1)$ which on every affine open are injective with image exactly $\ker(\varphi_k)_U$, the theorem asserts the existence of maps $\theta_{m,k}:K(k)\to K(k+1)$ (again `AffHom`s) such that: for all $m,k$, every affine open $U$, every $x\in K(k)(U)$ and every $y\in F(k+2)(U)$ with $(\varphi_{k+1})_U(y)=(j_k)_U(x)$ one has $(j_{k+1})_U((\theta_{m,k})_U(x))=g_m\cdot y$; the $\theta$'s commute, $(\theta_{m,k+1})_U\circ(\theta_{m',k})_U=(\theta_{m',k+1})_U\circ(\theta_{m,k})_U$ for all $m,m',k,U$; and for every $k$ and every affine open $U$ the supremum of the ranges of the $(\theta_{m,k})_U$, as $A$-submodules of $K(k+1)(U)$, is everything.
--
--   This is the statement that the associated graded of an $I$-adic system of module data carries commuting multiplication operators by a chosen generating set of $I$, and that these generate each graded piece from the previous one; in classical terms, the graded object is a graded module over a polynomial ring on $s$ variables, generated in degree zero. It feeds the subsequent vanishing statement [`AlgebraicGeometry.OModulePresheaf.exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top) for the Čech cohomology of tensor twists of such systems.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top
    {A : Type u} [CommRing A] (I : Ideal A) {s : ℕ} (g : Fin s → A) (hg : Ideal.span (Set.range g) = I)
    {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of A)}
    (F : ℕ → OModulePresheaf π) (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : V.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : V.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (K : ℕ → OModulePresheaf π) (j : ∀ k, OModulePresheaf.AffHom (K k) (F (k + 1)))
    (hji : ∀ (k : ℕ) (U : V.affineOpens), Function.Injective ((j k).app U))
    (hjr : ∀ (k : ℕ) (U : V.affineOpens), LinearMap.range ((j k).app U) = LinearMap.ker ((φ k).app U)) :
    ∃ θ : Fin s → ∀ k : ℕ, OModulePresheaf.AffHom (K k) (K (k + 1)),
      (∀ (m : Fin s) (k : ℕ) (U : V.affineOpens) (x : (K k).obj U.1) (y : (F (k + 1 + 1)).obj U.1),
          (φ (k + 1)).app U y = (j k).app U x → (j (k + 1)).app U ((θ m k).app U x) = g m • y) ∧
      (∀ (m m' : Fin s) (k : ℕ) (U : V.affineOpens) (x : (K k).obj U.1),
          (θ m (k + 1)).app U ((θ m' k).app U x) = (θ m' (k + 1)).app U ((θ m k).app U x)) ∧
      (∀ (k : ℕ) (U : V.affineOpens), (⨆ m : Fin s, LinearMap.range ((θ m k).app U)) = ⊤) := by sorry
