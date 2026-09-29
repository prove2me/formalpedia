-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top
-- name    : AlgebraicGeometry.OModulePresheaf.exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/75c64388-4704-5d6c-a232-34b892b06869
-- title:
--   Coimage of a morphism of I-adic systems of coherent data
-- statement:
--   Fix a commutative ring $A$, an ideal $I \subseteq A$, a scheme $P$ and a morphism $q : P \to \operatorname{Spec} A$. Here an `OModulePresheaf q` is a presheaf-like datum assigning to each open $U \subseteq P$ an $A$-module that is also a $\Gamma(P,U)$-module compatibly over $A$, together with $A$-linear restriction maps semilinear for restriction of sections and functorial; an `AffHom` is a family of $A$-linear maps on the sections over affine opens, $\Gamma(P,U)$-semilinear and compatible with restriction along inclusions of affine opens. `IsCoherent` means the sections over each affine open $U$ form a finite $\Gamma(P,U)$-module, and `IsQuasicoherent` means that for each affine open $U$ and each $f \in \Gamma(P,U)$, every section over the basic open $D(f)$ becomes, after multiplication by some power of $f$, the restriction of a section over $U$, and every section over $U$ restricting to $0$ on $D(f)$ is annihilated by some power of $f$. The data are: $F : \mathbb{N} \to$ `OModulePresheaf q` with each $F_k$ coherent and quasi-coherent, transition maps $\varphi_k : F_{k+1} \to F_k$ whose components at every affine open $U$ are surjective with kernel $I^{k+1} \cdot F_{k+1}(U)$; a second system $K$ with each $K_k$ quasi-coherent and transitions $\kappa_k : K_{k+1} \to K_k$ surjective at every affine open; maps $j_k : K_k \to F_k$ with $\varphi_k \circ j_{k+1} = j_k \circ \kappa_k$ at every affine open; a further system $Ps$ with transitions $\pi_k : Ps_{k+1} \to Ps_k$ (no coherence or quasi-coherence being assumed for it) and maps $u_k : F_k \to Ps_k$ satisfying $\pi_k \circ u_{k+1} = u_k \circ \varphi_k$ and $u_k \circ j_k = 0$ at every affine open; and an Artin–Rees hypothesis: for each affine open $U$ there is $c \in \mathbb{N}$ with $\ker u_{k+c}(U) \le \operatorname{im} j_{k+c}(U) + I^{k+1} \cdot F_{k+c}(U)$ for all $k$. The conclusion asserts the existence of a system $E : \mathbb{N} \to$ `OModulePresheaf q` with transitions $\tau_k : E_{k+1} \to E_k$ such that every $E_k$ is coherent and quasi-coherent, each $\tau_k$ is surjective at every affine open with kernel $I^{k+1} \cdot E_{k+1}(U)$; of maps $\varepsilon_k : F_k \to E_k$, surjective at every affine open, with $\tau_k \circ \varepsilon_{k+1} = \varepsilon_k \circ \varphi_k$ and $\ker \varepsilon_k(U) = \operatorname{im} j_k(U)$; and of maps $\bar u_k : E_k \to Ps_k$ with $\bar u_k \circ \varepsilon_k = u_k$, $\pi_k \circ \bar u_{k+1} = \bar u_k \circ \tau_k$, $\operatorname{im} \bar u_k(U) = \operatorname{im} u_k(U)$, and, for each affine open $U$, some $c$ with $\ker \bar u_{k+c}(U) \le I^{k+1} \cdot E_{k+c}(U)$ for all $k$.
--
--   This is the formation of the coimage of a morphism of $I$-adic systems of coherent data: one divides out the images of the $j_k$ and checks that the quotient system is again an $I$-adic system of coherent quasi-coherent data, that the given maps to the system $Ps$ factor through it, and that the Artin–Rees estimate improves to one without the image term. It feeds the proof of Grothendieck's existence theorem for proper morphisms over an $I$-adically complete base, where the system to be algebraised is built from such a coimage; the construction of the quotient at each level uses [`AlgebraicGeometry.OModulePresheaf.AffHom.exists_isQuasicoherent_surjective_ker_eq_range`](thm.html#AlgebraicGeometry.OModulePresheaf.AffHom.exists_isQuasicoherent_surjective_ker_eq_range).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top
    {A : Type u} [CommRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (K : ℕ → OModulePresheaf q) (hKq : ∀ k, (K k).IsQuasicoherent)
    (κ : ∀ k, OModulePresheaf.AffHom (K (k + 1)) (K k))
    (hκs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((κ k).app U))
    (j : ∀ k, OModulePresheaf.AffHom (K k) (F k))
    (hjc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (j (k + 1)).app U = (j k).app U ∘ₗ (κ k).app U)
    (Ps : ℕ → OModulePresheaf q) (π : ∀ k, OModulePresheaf.AffHom (Ps (k + 1)) (Ps k))
    (u : ∀ k, OModulePresheaf.AffHom (F k) (Ps k))
    (huc : ∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (u (k + 1)).app U = (u k).app U ∘ₗ (φ k).app U)
    (huj : ∀ (k : ℕ) (U : P.affineOpens), (u k).app U ∘ₗ (j k).app U = 0)
    (hAR : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((u (k + c)).app U)
        ≤ LinearMap.range ((j (k + c)).app U) ⊔ I ^ (k + 1) • (⊤ : Submodule A ((F (k + c)).obj U.1))) :
    ∃ (E : ℕ → OModulePresheaf q) (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k)),
      (∀ k, (E k).IsCoherent) ∧ (∀ k, (E k).IsQuasicoherent) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1))) ∧
      ∃ ε : ∀ k, OModulePresheaf.AffHom (F k) (E k),
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), LinearMap.ker ((ε k).app U) = LinearMap.range ((j k).app U)) ∧
      ∃ uE : ∀ k, OModulePresheaf.AffHom (E k) (Ps k),
      (∀ (k : ℕ) (U : P.affineOpens), (uE k).app U ∘ₗ (ε k).app U = (u k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (uE (k + 1)).app U = (uE k).app U ∘ₗ (τ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), LinearMap.range ((uE k).app U) = LinearMap.range ((u k).app U)) ∧
      (∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
        LinearMap.ker ((uE (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((E (k + c)).obj U.1))) := by sorry
