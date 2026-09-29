-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_mem_range_d_of_d_eq_zero_of_forall_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.mem_range_d_of_d_eq_zero_of_forall_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/f1b2b89a-6fe1-58fa-b388-6c48decd159b
-- title:
--   Cocycles trivial modulo every Iⁿ are coboundaries
-- statement:
--   Let $A$ be a commutative Noetherian ring, $I \subseteq A$ an ideal, and suppose $A$ is $I$-adically complete (Hausdorff and precomplete for the $I$-adic filtration). Let $q : P \to \operatorname{Spec} A$ be a proper morphism of schemes, and let $F$ be an `OModulePresheaf` over $q$, that is, an assignment to each open $U \subseteq P$ of an $A$-module $F.obj\,U$ which is also a $\Gamma(P,U)$-module compatibly with the $A$-algebra structure on $\Gamma(P,U)$ induced by $q$, together with $A$-linear restriction maps satisfying the semilinearity, reflexivity and transitivity identities. Assume $F$ is coherent in the sense that $F.obj\,U$ is a finite $\Gamma(P,U)$-module for every affine open $U$, and quasi-coherent in the sense that for every affine open $U$ and every $f \in \Gamma(P,U)$, each section over the basic open $D(f)$ becomes the restriction of a section over $U$ after multiplication by some power of $f$, and each section over $U$ restricting to $0$ on $D(f)$ is killed by some power of $f$. Let $K$ be an ordered affine cover of $P$: a finite linearly ordered index type together with affine opens covering $P$; the degree-$i$ cochains $F.cochain\,K\,i$ are the families, indexed by the degree-$i$ index set of $K$, of sections of $F$ over the corresponding intersections of members of the cover, with differentials $F.d\,K\,i$. Fix $i \in \mathbb{N}$ and a cochain $a$ of degree $i+1$ with $F.d\,K\,(i+1)\,a = 0$, and assume that for every $n \in \mathbb{N}$ one has $a \in I^{n+1} \cdot F.cochain\,K\,(i+1) + \operatorname{range}(F.d\,K\,i)$. Then $a$ lies in $\operatorname{range}(F.d\,K\,i)$.
--
--   This is the injectivity half of the theorem on formal functions in positive degree, in Čech form: a cocycle whose class dies in every truncation modulo $I^{n+1}$ is already a coboundary, equivalently $\check{H}^{i+1}(K,F) \to \varprojlim_n \check{H}^{i+1}(K, F/I^{n+1}F)$ is injective. It is used in the construction of cocycles over $I$-adically complete bases, via [`AlgebraicGeometry.OModulePresheaf.exists_cocycle_of_chartData_of_isProper_of_isAdicComplete`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_cocycle_of_chartData_of_isProper_of_isAdicComplete).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_mem_range_d_of_d_eq_zero_of_forall_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.mem_range_d_of_d_eq_zero_of_forall_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (i : ℕ) (a : F.cochain K (i + 1)) (ha : F.d K (i + 1) a = 0)
    (h : ∀ n : ℕ, a ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 1))) ⊔ LinearMap.range (F.d K i)) :
    a ∈ LinearMap.range (F.d K i) := by sorry
