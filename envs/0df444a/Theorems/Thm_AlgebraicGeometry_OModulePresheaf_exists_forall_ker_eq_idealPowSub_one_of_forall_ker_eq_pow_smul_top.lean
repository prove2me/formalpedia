-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top
-- name    : AlgebraicGeometry.OModulePresheaf.exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/92355728-3a17-5776-b5d6-0f65bab9f740
-- title:
--   Reduction of an I-adic system modulo an ideal sheaf
-- statement:
--   Let $A$ be a Noetherian commutative ring, $I \subseteq A$ an ideal, $P$ a scheme, $q : P \to \operatorname{Spec} A$ a morphism locally of finite type, and $\mathcal J$ ideal sheaf data on $P$. Let $F_k$, $k \in \mathbb N$, be module-presheaf data on the opens of $P$ relative to $q$ (an $A$-module and a $\Gamma(P,U)$-module on each open $U$, compatible via the algebra structure induced by $q$, together with restriction maps), each coherent, i.e. $F_k(U)$ is a finite $\Gamma(P,U)$-module for every affine open $U$, and each quasi-coherent in the sense that on every basic open $D(f)$ inside an affine open $U$ every section is $f^n$ times the restriction of a section over $U$, and every section over $U$ restricting to $0$ is killed by some $f^n$. Let $\varphi_k$ be affine-open morphisms $F_{k+1} \to F_k$ ($A$-linear maps on each affine open, compatible with multiplication by sections and with restriction) such that $\varphi_k(U)$ is surjective with kernel $I^{k+1} \cdot F_{k+1}(U)$ for every affine open $U$. The conclusion asserts the existence of module-presheaf data $Q_k$, affine-open morphisms $\tau_k : Q_{k+1} \to Q_k$ and $\varepsilon_k : F_k \to Q_k$ such that: every $Q_k$ is coherent and quasi-coherent; each $\tau_k(U)$ is surjective with kernel $I^{k+1} \cdot Q_{k+1}(U)$; the squares commute, $\tau_k(U) \circ \varepsilon_{k+1}(U) = \varepsilon_k(U) \circ \varphi_k(U)$; each $\varepsilon_k(U)$ is surjective with kernel the $A$-submodule $\mathcal J(U) \cdot F_k(U)$, where $\mathcal J(U)$ is the kernel of the map $\Gamma(P,U) \to \Gamma$ of the closed subscheme attached to $\mathcal J$; and each $Q_k$ is annihilated by $\mathcal J$, i.e. $a \cdot x = 0$ for every affine open $U$, every $a$ in the ideal of $\mathcal J$ at $U$ and every $x \in Q_k(U)$.
--
--   This is the statement that the category of $I$-adic systems of coherent modules is stable under reduction modulo a quasi-coherent ideal sheaf: the quotients $F_k/\mathcal J F_k$ again form a system with surjective transition maps whose kernels are $I^{k+1}$ times the module, and they are annihilated by $\mathcal J$. It is cited by [`AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isProper_of_isAdicComplete), where the Noetherian induction behind Grothendieck's existence theorem for proper morphisms passes from $P$ to the closed subscheme cut out by $\mathcal J$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_ker_eq_idealPowSub_one_of_forall_ker_eq_pow_smul_top
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)} [LocallyOfFiniteType q] (𝓙 : P.IdealSheafData)
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1))) :
    ∃ (Q : ℕ → OModulePresheaf q) (τ : ∀ k, OModulePresheaf.AffHom (Q (k + 1)) (Q k))
      (ε : ∀ k, OModulePresheaf.AffHom (F k) (Q k)),
      (∀ k, (Q k).IsCoherent) ∧ (∀ k, (Q k).IsQuasicoherent) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Q (k + 1)).obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ε k).app U) = OModulePresheaf.idealPowSub q 𝓙 (F k) 1 U.1) ∧
      (∀ k, OModulePresheaf.IdealAnnihilates q 𝓙 (Q k)) := by sorry
