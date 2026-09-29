-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_forall_subsingleton_HSucc_restrict_of_subsingleton_HTot_biCech
-- name    : AlgebraicGeometry.OModulePresheaf.H0_eq_bot_and_forall_subsingleton_HSucc_restrict_of_subsingleton_HTot_biCech
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/2c160864-4876-5d63-b84e-5af948e9861a
-- title:
--   Čech acyclicity on V from acyclicity of the glued cover
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $\pi\colon X\to\operatorname{Spec} R$ a morphism, $N$ an $\mathcal O_X$-module, and $U,V$ two open subsets of $X$. Let $\mathfrak V$ and $\mathfrak U$ be finite ordered affine open covers of the open subschemes $V$ and $U$, and $\mathfrak X'$ one of $X$, together with order embeddings $e_V\colon\mathfrak V.\iota\hookrightarrow\mathfrak X'.\iota$ and $e_U\colon\mathfrak U.\iota\hookrightarrow\mathfrak X'.\iota$ such that $\mathfrak X'.U(e_V b)$ is the image of $\mathfrak V.U\,b$ under $V.\iota$, $\mathfrak X'.U(e_U a)$ is the image of $\mathfrak U.U\,a$ under $U.\iota$, every $e_V b$ is strictly less than every $e_U a$, and every index of $\mathfrak X'$ lies in the range of $e_V$ or of $e_U$. Assume that for the presheaf of modules $U'\mapsto\Gamma(N,U')$ attached to $\pi$ and $N$ the Čech complex of $\mathfrak X'$ is acyclic, i.e. the kernel of its $0$-th differential is $\bot$ and each quotient $\ker d^{i+1}/\operatorname{im} d^{i}$ is a subsingleton, and that every total cohomology module $\mathrm{HTot}_n$ of the bi-Čech double complex of that presheaf formed from the image families $\mathfrak V.\mathrm{imageFamily}\,V.\iota$ and $\mathfrak U.\mathrm{imageFamily}\,U.\iota$ is a subsingleton. Then the analogous presheaf attached to $V.\iota$ followed by $\pi$ and to $N|_V$ has vanishing Čech cohomology for $\mathfrak V$: the kernel of its $0$-th differential is $\bot$ and each $\ker d^{i+1}/\operatorname{im} d^{i}$ is a subsingleton.
--
--   This is the Mayer–Vietoris step for alternating Čech cohomology in the form needed here: the cochains of the glued cover $\mathfrak X'$ of $X=U\cup V$ supported on mixed simplices form a subcomplex computed by the total complex of the mixed bi-Čech double complex, and acyclicity of both the glued Čech complex and that total complex forces the Čech complex of $\mathfrak V$ to be acyclic. It feeds the reduction of Čech acyclicity statements to a two-chart situation, being used by [`AlgebraicGeometry.OModulePresheaf.forall_subsingleton_HSucc_restrict_of_sup_eq_top`](thm.html#AlgebraicGeometry.OModulePresheaf.forall_subsingleton_HSucc_restrict_of_sup_eq_top); only the relation $d^{i+1}\circ d^{i}=0$ for Čech differentials is invoked from elsewhere in the project.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_forall_subsingleton_HSucc_restrict_of_subsingleton_HTot_biCech.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BiCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.H0_eq_bot_and_forall_subsingleton_HSucc_restrict_of_subsingleton_HTot_biCech
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R))
    (N : X.Modules) (U V : X.Opens)
    (𝔙 : (V : Scheme.{u}).OrderedAffineCover) (𝔘 : (U : Scheme.{u}).OrderedAffineCover)
    (𝔛' : X.OrderedAffineCover) (eV : 𝔙.ι ↪o 𝔛'.ι) (eU : 𝔘.ι ↪o 𝔛'.ι)
    (hV : ∀ b, 𝔛'.U (eV b) = V.ι ''ᵁ 𝔙.U b) (hU : ∀ a, 𝔛'.U (eU a) = U.ι ''ᵁ 𝔘.U a)
    (hlt : ∀ b a, eV b < eU a) (hcov : ∀ j, j ∈ Set.range eV ∨ j ∈ Set.range eU)
    (hX : (OModulePresheaf.ofModules π N).H0 𝔛' = ⊥ ∧
      ∀ i, Subsingleton ((OModulePresheaf.ofModules π N).HSucc 𝔛' i))
    (hD : ∀ n, Subsingleton (DoubleComplex.HTot
      ((OModulePresheaf.ofModules π N).biCech (𝔙.imageFamily V.ι) (𝔘.imageFamily U.ι)) n)) :
    (OModulePresheaf.ofModules (V.ι ≫ π) (N.restrict V.ι)).H0 𝔙 = ⊥ ∧
      ∀ i, Subsingleton ((OModulePresheaf.ofModules (V.ι ≫ π) (N.restrict V.ι)).HSucc 𝔙 i) := by sorry
