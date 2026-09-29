-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete
-- name    : AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/89cb523c-9358-5dfa-84f8-a94f88207b2d
-- title:
--   Algebraisability of kernels in adic systems on proper schemes
-- statement:
--   Let $A$ be a Noetherian ring, $I \subseteq A$ an ideal for which $A$ is $I$-adically complete, and let $q : P \to \operatorname{Spec} A$ be a proper morphism of schemes. Sheaf-like data on $P$ are taken in the form of an `OModulePresheaf` for $q$: an assignment of an $A$-module and $\Gamma(P,U)$-module structure (compatibly, via the $A$-algebra structure induced by $q$) to each open $U$, together with $A$-linear restriction maps satisfying the semilinearity, reflexivity and transitivity laws; `IsCoherent` means that on every affine open $U$ the module of sections is a finite $\Gamma(P,U)$-module, and `IsQuasicoherent` means that for every affine open $U$ and every $f \in \Gamma(P,U)$ each section over the basic open $P_f$ becomes, after multiplication by some power of $f$, the restriction of a section over $U$, and each section over $U$ restricting to $0$ on $P_f$ is annihilated by some power of $f$. Morphisms are `AffHom`s: families of $A$-linear maps on the modules of sections over affine opens, semilinear for the action of sections and commuting with restriction along inclusions of affine opens. Given three families $(E_k)$, $(Ps_k)$, $(Cs_k)$ of coherent, quasi-coherent such data indexed by $k \in \mathbb{N}$, with transition `AffHom`s $\tau_k : E_{k+1} \to E_k$, $\pi_k : Ps_{k+1} \to Ps_k$, $\gamma_k : Cs_{k+1} \to Cs_k$ which on every affine open $U$ are surjective with kernel $I^{k+1}$ times the whole module of sections of the $(k+1)$-st term; given `AffHom`s $\theta_k : Ps_k \to Cs_k$ and $u_k : E_k \to Ps_k$ commuting on affine opens with the transitions ($\gamma_k \circ \theta_{k+1} = \theta_k \circ \pi_k$, $\pi_k \circ u_{k+1} = u_k \circ \tau_k$), such that on every affine open $U$ and every $k$ the range of $u_k$ is the kernel of $\theta_k$, and such that for every affine open $U$ there is $c \in \mathbb{N}$ with $\ker u_{k+c} \leq I^{k+1} \cdot E_{k+c}(U)$ for all $k$; and given coherent, quasi-coherent $GP$ and $GC$ with `AffHom`s $\psi P_k : GP \to Ps_k$ and $\psi C_k : GC \to Cs_k$ that on every affine open are surjective with kernels $I^{k+1} \cdot GP(U)$, respectively $I^{k+1} \cdot GC(U)$, and are compatible with the transitions ($\pi_k \circ \psi P_{k+1} = \psi P_k$, $\gamma_k \circ \psi C_{k+1} = \psi C_k$): then there exist coherent, quasi-coherent data $G$ for $q$ and `AffHom`s $\psi_k : G \to E_k$ which on every affine open $U$ are surjective with kernel $I^{k+1} \cdot G(U)$ and satisfy $\tau_k \circ \psi_{k+1} = \psi_k$.
--
--   This is the kernel step in the proof that algebraisable adic systems of coherent sheaves on a proper scheme over a complete Noetherian base form a class closed under passing to kernels: if the target systems $(Ps_k)$ and $(Cs_k)$ of a morphism $\theta$ are algebraised by $GP$ and $GC$, and $(E_k)$ maps onto $\ker \theta$ levelwise with kernels that are adically small, then $(E_k)$ is algebraised too. It feeds the general algebraisation statement [`AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete), used to obtain existence of formal deformation-theoretic objects in the modularity-lifting part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (Ps : ℕ → OModulePresheaf q) (hPsc : ∀ k, (Ps k).IsCoherent) (hPsq : ∀ k, (Ps k).IsQuasicoherent)
    (π : ∀ k, OModulePresheaf.AffHom (Ps (k + 1)) (Ps k))
    (hπs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((π k).app U))
    (hπk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((π k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + 1)).obj U.1)))
    (Cs : ℕ → OModulePresheaf q) (hCsc : ∀ k, (Cs k).IsCoherent) (hCsq : ∀ k, (Cs k).IsQuasicoherent)
    (γ : ∀ k, OModulePresheaf.AffHom (Cs (k + 1)) (Cs k))
    (hγs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((γ k).app U))
    (hγk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((γ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Cs (k + 1)).obj U.1)))
    (θ : ∀ k, OModulePresheaf.AffHom (Ps k) (Cs k))
    (hθc : ∀ (k : ℕ) (U : P.affineOpens), (γ k).app U ∘ₗ (θ (k + 1)).app U = (θ k).app U ∘ₗ (π k).app U)
    (u : ∀ k, OModulePresheaf.AffHom (E k) (Ps k))
    (huc : ∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (u (k + 1)).app U = (u k).app U ∘ₗ (τ k).app U)
    (hur : ∀ (k : ℕ) (U : P.affineOpens), LinearMap.range ((u k).app U) = LinearMap.ker ((θ k).app U))
    (hui : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((u (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((E (k + c)).obj U.1)))
    (GP : OModulePresheaf q) (hGPc : GP.IsCoherent) (hGPq : GP.IsQuasicoherent)
    (ψP : ∀ k, OModulePresheaf.AffHom GP (Ps k))
    (hψPs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψP k).app U))
    (hψPk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψP k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GP.obj U.1)))
    (hψPc : ∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (ψP (k + 1)).app U = (ψP k).app U)
    (GC : OModulePresheaf q) (hGCc : GC.IsCoherent) (hGCq : GC.IsQuasicoherent)
    (ψC : ∀ k, OModulePresheaf.AffHom GC (Cs k))
    (hψCs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψC k).app U))
    (hψCk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψC k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GC.obj U.1)))
    (hψCc : ∀ (k : ℕ) (U : P.affineOpens), (γ k).app U ∘ₗ (ψC (k + 1)).app U = (ψC k).app U) :
    ∃ (G : OModulePresheaf q) (ψ : ∀ k, OModulePresheaf.AffHom G (E k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) := by sorry
