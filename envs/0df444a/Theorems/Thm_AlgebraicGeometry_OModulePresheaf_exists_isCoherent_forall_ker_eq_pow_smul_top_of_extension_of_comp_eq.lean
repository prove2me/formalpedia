-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_extension_of_comp_eq
-- name    : AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_extension_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/170dfc68-1832-59ec-a543-4fa9acf57a60
-- title:
--   Algebraisation of an adic system from a morphism of extensions
-- statement:
--   Let $A$ be a Noetherian commutative ring, $I \subseteq A$ an ideal with $A$ $I$-adically complete, and $q : P \to \operatorname{Spec} A$ a proper morphism of schemes. Throughout, an `OModulePresheaf q` is a presheaf $U \mapsto \mathcal M(U)$ on the opens of $P$ carrying compatible $A$- and $\Gamma(P,U)$-module structures with $A$-linear restriction maps satisfying the presheaf identities; `IsCoherent` means $\mathcal M(U)$ is a finite $\Gamma(P,U)$-module for every affine open $U$; `IsQuasicoherent` means that on every affine open $U$ and $f \in \Gamma(P,U)$, every section over $P_f$ becomes $f^n$ times the restriction of a section over $U$, and every section over $U$ restricting to $0$ on $P_f$ is killed by some $f^n$; and an `AffHom` is a family of $\Gamma(P,U)$-semilinear $A$-linear maps indexed by affine opens, commuting with restrictions. The data are: coherent quasi-coherent systems $(F_k)_{k \in \mathbb N}$ and $(E_k)_{k \in \mathbb N}$ with transition maps $\varphi_k : F_{k+1} \to F_k$, $\tau_k : E_{k+1} \to E_k$ that are surjective on each affine open $U$ with kernel $I^{k+1} \cdot F_{k+1}(U)$, respectively $I^{k+1} \cdot E_{k+1}(U)$; maps $\varepsilon_k : F_k \to E_k$, surjective on each affine open, with $\tau_k \circ \varepsilon_{k+1} = \varepsilon_k \circ \varphi_k$; a coherent quasi-coherent $G_E$ with $\psi^E_k : G_E \to E_k$ surjective on each affine open, of kernel $I^{k+1} \cdot G_E(U)$, and $\tau_k \circ \psi^E_{k+1} = \psi^E_k$; a coherent quasi-coherent $G_K$ with $\lambda_k : G_K \to F_k$ satisfying $\varphi_k \circ \lambda_{k+1} = \lambda_k$, $\operatorname{im} \lambda_k = \ker \varepsilon_k$ on each affine open, and, for each affine open $U$, some $c$ with $\ker \lambda_{k+c} \subseteq I^{k+1} \cdot G_K(U)$ for all $k$; and a coherent quasi-coherent $G$ with $\alpha : G_K \to G$, $\beta : G \to G_E$ such that $\operatorname{im} \alpha = \ker \beta$ and $\beta$ is surjective on each affine open, together with $\psi_k : G \to F_k$ satisfying $\varphi_k \circ \psi_{k+1} = \psi_k$, $\psi_k \circ \alpha = \lambda_k$ and $\varepsilon_k \circ \psi_k = \psi^E_k \circ \beta$ on each affine open. The conclusion asserts the existence of a coherent quasi-coherent $\mathcal G$ together with maps $\psi_k : \mathcal G \to F_k$ that are surjective on every affine open $U$, have kernel exactly $I^{k+1} \cdot \mathcal G(U)$ there, and satisfy $\varphi_k \circ \psi_{k+1} = \psi_k$ (the bound variables $\mathcal G$, $\psi$ of the conclusion shadowing the hypotheses' $G$, $\psi$).
--
--   This is the levelwise step in Grothendieck's existence theorem for proper morphisms over an adically complete Noetherian base: given an extension of adic systems whose sub- and quotient systems are already algebraised, a middle term mapping compatibly to the system is itself an algebraisation. It feeds the existence statement [`AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_extension_of_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_extension_of_comp_eq
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))
    (G : OModulePresheaf q) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (α : OModulePresheaf.AffHom GK G) (β : OModulePresheaf.AffHom G GE)
    (hαβ : ∀ U : P.affineOpens, LinearMap.range (α.app U) = LinearMap.ker (β.app U))
    (hβs : ∀ U : P.affineOpens, Function.Surjective (β.app U))
    (ψ : ∀ k, OModulePresheaf.AffHom G (F k))
    (hψc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U)
    (hψα : ∀ (k : ℕ) (U : P.affineOpens), (ψ k).app U ∘ₗ α.app U = (lam k).app U)
    (hψβ : ∀ (k : ℕ) (U : P.affineOpens), (ε k).app U ∘ₗ (ψ k).app U = (ψE k).app U ∘ₗ β.app U) :
    ∃ (G : OModulePresheaf q) (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) := by sorry
