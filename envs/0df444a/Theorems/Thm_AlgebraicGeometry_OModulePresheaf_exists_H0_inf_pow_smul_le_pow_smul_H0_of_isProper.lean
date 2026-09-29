-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/1fbbdeee-f9c4-58ce-a2de-499586afa655
-- title:
--   Degree-zero theorem on formal functions: separatedness half
-- statement:
--   Let $A$ be a Noetherian commutative ring, $I \subseteq A$ an ideal, and let $q : P \to \operatorname{Spec} A$ be a proper morphism of schemes. Let $F$ be an $\mathcal O$-module presheaf over $q$: an assignment of an abelian group $F.\mathrm{obj}\,U$ to each open $U \subseteq P$, carrying compatible module structures over $A$ and over $\Gamma(P,U)$ (the $A$-algebra structure on $\Gamma(P,U)$ being the one induced by $q$), together with $A$-linear restriction maps that are semilinear for restriction of functions and functorial. Assume $F$ is coherent, i.e. $F.\mathrm{obj}\,U$ is a finite $\Gamma(P,U)$-module for every affine open $U$, and quasi-coherent in the sense that for every affine open $U$ and every $f \in \Gamma(P,U)$, each element of $F.\mathrm{obj}\,(D(f))$ becomes $f^{n}$ times the restriction of a section over $U$ for some $n$, and every section over $U$ restricting to $0$ on $D(f)$ is annihilated by some $f^{n}$. Let $K$ be an ordered affine cover of $P$, that is a finite linearly ordered index set together with affine opens $U_i$ whose supremum is $P$, and let $n \in \mathbb N$. Then there is $c \in \mathbb N$ such that the intersection of the $A$-submodule $F.H0\,K$ of the degree-zero cochain module $F.\mathrm{cochain}\,K\,0 = \prod_{s} F.\mathrm{obj}(\bigcap_j U_{s(j)})$ with $I^{n+c} \cdot F.\mathrm{cochain}\,K\,0$ is contained in $I^{n} \cdot F.H0\,K$.
--
--   This is the separatedness (injectivity) half of Grothendieck's theorem on formal functions in degree zero, in the Čech form: sections of a coherent sheaf on a proper $A$-scheme that are divisible by $I^{n+c}$ chartwise are divisible by $I^{n}$ globally. It is used in the project's statements of $I$-adic comparison and existence results over adically complete bases, namely `existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper`, `existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper` and `exists_forall_eq_sum_smul_of_forall_mem_pow_smul_preimage_of_isProper`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (n : ℕ) :
    ∃ c : ℕ, F.H0 K ⊓ I ^ (n + c) • (⊤ : Submodule A (F.cochain K 0)) ≤ I ^ n • F.H0 K := by sorry
