-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top
-- name    : AlgebraicGeometry.OModulePresheaf.exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/1eb0e70b-4c5f-5cdf-b562-edce7438a4dc
-- title:
--   Stable kernel of a morphism of I-adic systems of coherent sheaves
-- statement:
--   Let $A$ be a commutative Noetherian ring, $I \subseteq A$ an ideal, and $q : P \to \operatorname{Spec} A$ a morphism of schemes that is locally of finite type. Let $F : \mathbb{N} \to$ `OModulePresheaf q` and $Ps : \mathbb{N} \to$ `OModulePresheaf q` be families of module data over $q$ (each assigning to every open $U$ of $P$ an $A$-module that is also a $\Gamma(P,U)$-module compatibly, together with $A$-linear restriction maps), each term coherent (finite as a $\Gamma(P,U)$-module on every affine open $U$) and quasicoherent (the two basic-open conditions: every section over $P_f \cap U$ becomes the restriction of a section over $U$ after multiplication by some $f^n$, and a section over $U$ restricting to $0$ is killed by some $f^n$). Let $\varphi_k : F(k+1) \to F(k)$ and $\pi_k : Ps(k+1) \to Ps(k)$ be `AffHom`s, i.e. families of $A$-linear maps on affine opens that are $\Gamma(P,U)$-semilinear and commute with restriction; assume each is surjective on every affine open $U$ with kernel $I^{k+1} \cdot (F(k+1))(U)$, respectively $I^{k+1} \cdot (Ps(k+1))(U)$. Let $u_k : F(k) \to Ps(k)$ be `AffHom`s with $\pi_k \circ u_{k+1} = u_k \circ \varphi_k$ on every affine open. The conclusion asserts the existence of module data $L : \mathbb{N} \to$ `OModulePresheaf q` together with `AffHom`s $\iota_n : L(n) \to F(n)$ and $\lambda_n : L(n+1) \to L(n)$ such that: every $L(n)$ is coherent and quasicoherent; each $\iota_n$ is injective on every affine open; each $\lambda_n$ is surjective on every affine open; $\iota_n \circ \lambda_n = \varphi_n \circ \iota_{n+1}$ and $u_n \circ \iota_n = 0$ on every affine open; for every affine open $U$ there is $c \in \mathbb{N}$ such that for all $k, n$ with $k + c \le n$ one has $\ker(u_n)_U \le \operatorname{range}(\iota_n)_U + I^{k+1}\cdot (F(n))(U)$ and $I^{n}\cdot (F(n))(U) \cap \operatorname{range}(\iota_n)_U \le I^{k}\cdot \operatorname{range}(\iota_n)_U$; and, if moreover every $u_n$ is surjective on every affine open, then $\operatorname{range}(\iota_n)_U = \ker(u_n)_U$ for all $n$ and all affine opens $U$.
--
--   This is the sheaf-level form of the stable-kernel (Artin–Rees type) lemma for morphisms of $I$-adic systems of coherent modules: the subsystem $L$ plays the role of the system of stable kernels of $u$, with transition maps surjective and with the kernels of $u_n$ recovered up to $I$-adic error, exactly on the nose when $u$ is surjective. It rests on the module-theoretic statement [`Ideal.exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top`](thm.html#Ideal.exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top) over a Noetherian ring, and is used in the construction of kernel and cokernel adic systems in [`AlgebraicGeometry.OModulePresheaf.exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)} [LocallyOfFiniteType q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (Ps : ℕ → OModulePresheaf q) (hPsc : ∀ k, (Ps k).IsCoherent) (hPsq : ∀ k, (Ps k).IsQuasicoherent)
    (π : ∀ k, OModulePresheaf.AffHom (Ps (k + 1)) (Ps k))
    (hπs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((π k).app U))
    (hπk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((π k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + 1)).obj U.1)))
    (u : ∀ k, OModulePresheaf.AffHom (F k) (Ps k))
    (huc : ∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (u (k + 1)).app U = (u k).app U ∘ₗ (φ k).app U) :
    ∃ (L : ℕ → OModulePresheaf q) (ι : ∀ n, OModulePresheaf.AffHom (L n) (F n))
      (lam : ∀ n, OModulePresheaf.AffHom (L (n + 1)) (L n)),
      (∀ n, (L n).IsCoherent) ∧ (∀ n, (L n).IsQuasicoherent) ∧
      (∀ (n : ℕ) (U : P.affineOpens), Function.Injective ((ι n).app U)) ∧
      (∀ (n : ℕ) (U : P.affineOpens), Function.Surjective ((lam n).app U)) ∧
      (∀ (n : ℕ) (U : P.affineOpens), (ι n).app U ∘ₗ (lam n).app U = (φ n).app U ∘ₗ (ι (n + 1)).app U) ∧
      (∀ (n : ℕ) (U : P.affineOpens), (u n).app U ∘ₗ (ι n).app U = 0) ∧
      (∀ U : P.affineOpens, ∃ c : ℕ, ∀ k n : ℕ, k + c ≤ n →
        LinearMap.ker ((u n).app U) ≤ LinearMap.range ((ι n).app U) ⊔ I ^ (k + 1) • (⊤ : Submodule A ((F n).obj U.1)) ∧
        I ^ n • (⊤ : Submodule A ((F n).obj U.1)) ⊓ LinearMap.range ((ι n).app U) ≤ I ^ k • LinearMap.range ((ι n).app U)) ∧
      ((∀ (n : ℕ) (U : P.affineOpens), Function.Surjective ((u n).app U)) →
        ∀ (n : ℕ) (U : P.affineOpens), LinearMap.range ((ι n).app U) = LinearMap.ker ((u n).app U)) := by sorry
