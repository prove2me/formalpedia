-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
-- name    : AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/609e3c32-4019-5a44-95ce-0ee8dc0482a8
-- title:
--   Algebraisability of adic systems is stable under extensions
-- statement:
--   Let $A$ be a Noetherian commutative ring with an ideal $I$ such that $A$ is $I$-adically complete, and let $q : P \to \operatorname{Spec} A$ be a proper morphism of schemes. Here an `OModulePresheaf q` assigns to each open $U \subseteq P$ an $A$-module that is also a $\Gamma(P,U)$-module compatibly over $A$, together with $A$-linear restriction maps semilinear for the restriction of sections and functorial; such an object is `IsCoherent` when each $F(U)$, for $U$ affine open, is a finite $\Gamma(P,U)$-module, and `IsQuasicoherent` when for every affine open $U$ and $f \in \Gamma(P,U)$ every section over the basic open $P_f$ becomes, after multiplication by some $f^n$, a restriction, and every section over $U$ restricting to $0$ on $P_f$ is killed by some $f^n$; an `AffHom` is a family of $A$-linear maps on affine opens, semilinear for sections and commuting with restrictions. Given: coherent quasi-coherent systems $(F_k,\varphi_k)$ and $(E_k,\tau_k)$ indexed by $\mathbb N$, whose transition maps are surjective on every affine open $U$ with kernels $I^{k+1} \cdot F_{k+1}(U)$, resp. $I^{k+1} \cdot E_{k+1}(U)$; maps $\varepsilon_k : F_k \to E_k$, surjective on affine opens and with $\tau_k \circ \varepsilon_{k+1} = \varepsilon_k \circ \varphi_k$; a coherent quasi-coherent $GE$ with maps $\psi^E_k : GE \to E_k$, surjective on affine opens, of kernel $I^{k+1} \cdot GE(U)$ and with $\tau_k \circ \psi^E_{k+1} = \psi^E_k$; and a coherent quasi-coherent $GK$ with maps $\lambda_k : GK \to F_k$ satisfying $\varphi_k \circ \lambda_{k+1} = \lambda_k$, $\operatorname{im}(\lambda_k(U)) = \ker(\varepsilon_k(U))$ on every affine open $U$, and, for each affine open $U$, some $c$ with $\ker(\lambda_{k+c}(U)) \subseteq I^{k+1} \cdot GK(U)$ for all $k$. Then there exist a coherent quasi-coherent $G$ and maps $\psi_k : G \to F_k$ that are surjective on every affine open $U$, have kernel $I^{k+1} \cdot G(U)$ there, and satisfy $\varphi_k \circ \psi_{k+1} = \psi_k$.
--
--   This is the extension step in Grothendieck's existence theorem in formal geometry: if the sub- and quotient systems of an $I$-adic system of coherent sheaves on a proper scheme over an $I$-adically complete Noetherian base are algebraisable, so is the system itself. It feeds the induction that establishes algebraisability of adic systems in general, [`AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory
open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
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
    ∃ (G : OModulePresheaf q) (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) := by sorry
