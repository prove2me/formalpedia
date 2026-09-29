-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
-- name    : AlgebraicGeometry.OModulePresheaf.exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/c7806d8b-3f26-584d-b292-91a20568831f
-- title:
--   Algebraisation of an extension of formal coherent systems over a proper adic-complete base
-- statement:
--   Let $A$ be a Noetherian commutative ring, $I \subseteq A$ an ideal with $A$ $I$-adically complete, and let $q : P \to \operatorname{Spec} A$ be a proper morphism of schemes. Throughout, an `OModulePresheaf` over $q$ is a presheaf-like datum assigning to each open $U$ of $P$ an $A$-module that is also a $\Gamma(P,U)$-module compatibly over $A$, together with $A$-linear restriction maps that are semilinear for restriction of sections and functorial; `IsCoherent` means that over every affine open $U$ the module is a finite $\Gamma(P,U)$-module, and `IsQuasicoherent` means that for every affine open $U$ and $f \in \Gamma(P,U)$ each section over the basic open $D(f)$ becomes, after multiplication by some $f^n$, a restriction from $U$, and each section over $U$ restricting to $0$ on $D(f)$ is annihilated by some $f^n$; an `AffHom` is a family of $A$-linear maps on affine opens, compatible with multiplication by sections and with restrictions. Given such data: coherent quasi-coherent $F_k$ with maps $\varphi_k : F_{k+1} \to F_k$ that are surjective on every affine open $U$ with kernel $I^{k+1} \cdot F_{k+1}(U)$; likewise coherent quasi-coherent $E_k$ with $\tau_k : E_{k+1} \to E_k$ surjective with kernel $I^{k+1} \cdot E_{k+1}(U)$; maps $\varepsilon_k : F_k \to E_k$, surjective on affine opens, with $\tau_k \circ \varepsilon_{k+1} = \varepsilon_k \circ \varphi_k$; a coherent quasi-coherent $G_E$ with $\psi^E_k : G_E \to E_k$ surjective on affine opens, with kernel $I^{k+1} \cdot G_E(U)$ and $\tau_k \circ \psi^E_{k+1} = \psi^E_k$; and a coherent quasi-coherent $G_K$ with $\lambda_k : G_K \to F_k$ satisfying $\varphi_k \circ \lambda_{k+1} = \lambda_k$, $\operatorname{im}(\lambda_k|_U) = \ker(\varepsilon_k|_U)$ on every affine open $U$, and, for each affine open $U$, $\ker(\lambda_{k+c}|_U) \subseteq I^{k+1} \cdot G_K(U)$ for all $k$ and some $c = c(U)$. The conclusion asserts the existence of an `OModulePresheaf` $G$ over $q$, which is coherent and quasi-coherent, together with $\alpha : G_K \to G$, $\beta : G \to G_E$ and a family $\psi_k : G \to F_k$ such that on every affine open $U$ one has $\operatorname{im}(\alpha|_U) = \ker(\beta|_U)$ with $\beta|_U$ surjective, and $\varphi_k \circ \psi_{k+1} = \psi_k$, $\psi_k \circ \alpha = \lambda_k$, $\varepsilon_k \circ \psi_k = \psi^E_k \circ \beta$ for all $k$. No injectivity of $\alpha$ is asserted, and all exactness and compatibility conditions, in the hypotheses as in the conclusion, are stated on affine opens only.
--
--   This is the extension-theoretic form of Grothendieck's existence theorem in formal geometry: an extension of a formal system $(E_k)$ by $(F_k)$-data, already algebraised on the quotient and sub sides by $G_E$ and $G_K$, is algebraised by a single coherent module $G$ over the proper adic-complete base. It feeds the construction of an algebraised coherent module whose transition kernels are exactly the $I$-power multiples, used in the deformation-theoretic part of the modularity-lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
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
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1))) :
    ∃ (G : OModulePresheaf q) (α : OModulePresheaf.AffHom GK G) (β : OModulePresheaf.AffHom G GE)
      (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ U : P.affineOpens, LinearMap.range (α.app U) = LinearMap.ker (β.app U)) ∧
      (∀ U : P.affineOpens, Function.Surjective (β.app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (ψ k).app U ∘ₗ α.app U = (lam k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (ε k).app U ∘ₗ (ψ k).app U = (ψE k).app U ∘ₗ β.app U) := by sorry
