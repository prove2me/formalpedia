-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/9b94228a-c8e4-5d1b-ace0-b1694952c4a9
-- title:
--   Uniform Mittag-Leffler property for Čech 0-cochains, proper case
-- statement:
--   Let $A$ be a Noetherian commutative ring, $I \subseteq A$ an ideal, $P$ a scheme and $q : P \to \operatorname{Spec} A$ a proper morphism. Let $F$ be an `OModulePresheaf` over $q$: an assignment of an $A$-module `F.obj U` to each open $U \subseteq P$, carrying a compatible $\Gamma(P,U)$-module structure (compatibly with the $A$-algebra structure on $\Gamma(P,U)$ coming from $q$), together with $A$-linear restriction maps `F.res` which are semilinear for the restriction of sections, reflexive and transitive. Assume $F$ is coherent, i.e. `F.obj U` is a finite $\Gamma(P,U)$-module for every affine open $U$, and quasicoherent, i.e. for every affine open $U$ and every $f \in \Gamma(P,U)$ each section over the basic open $D(f)$ becomes, after multiplication by some power of $f$, the restriction of a section over $U$, and every section over $U$ whose restriction to $D(f)$ vanishes is annihilated by some power of $f$. Let $K$ be an ordered affine cover of $P$: a finite linearly ordered index type with affine opens $U_i$ whose supremum is $\top$, and let $n \in \mathbb{N}$. Then there exists $c \in \mathbb{N}$ such that for every $0$-cochain $t \in$ `F.cochain K 0` $= \prod_{s}$ `F.obj (K.inter s)` (the product over the degree-$0$ index set of $K$, `K.inter s` being the intersection of the cover opens indexed by $s$), if the Čech differential `F.d K 0 t` lies in $I^{n+c}$ times the full $A$-submodule of $1$-cochains, then there is a $0$-cochain $a$ with `F.d K 0 a = 0` and $t - a$ in $I^{n}$ times the full $A$-submodule of $0$-cochains.
--
--   This is the degree-$0$ instance of the uniform Artin–Rees (Mittag-Leffler) estimate underlying the theorem on formal functions: modulo $I^{n}$, Čech $0$-cochains that are cocycles modulo $I^{n+c}$ are already congruent to genuine $0$-cocycles, so that the image of $\check H^0(F/I^{n+c}F) \to \check H^0(F/I^{n}F)$ coincides with the image of $\check H^0(F)$. It is obtained from the corresponding statement for the structure sheaf, [`AlgebraicGeometry.OModulePresheaf.exists_d_eq_d_of_forall_d_mem_pow_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_d_eq_d_of_forall_d_mem_pow_of_isProper), and is used in the $I$-adically complete setting to produce sections of $F$ from compatible systems of sections modulo powers of $I$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (n : ℕ) :
    ∃ c : ℕ, ∀ t : F.cochain K 0,
      F.d K 0 t ∈ I ^ (n + c) • (⊤ : Submodule A (F.cochain K 1)) →
      ∃ a : F.cochain K 0, F.d K 0 a = 0 ∧ t - a ∈ I ^ n • (⊤ : Submodule A (F.cochain K 0)) := by sorry
