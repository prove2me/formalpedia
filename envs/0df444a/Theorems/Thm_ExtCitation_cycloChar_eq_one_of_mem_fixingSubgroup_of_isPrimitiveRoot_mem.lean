-- Prove2me | Theorems.Thm_ExtCitation_cycloChar_eq_one_of_mem_fixingSubgroup_of_isPrimitiveRoot_mem
-- name    : ExtCitation.cycloChar_eq_one_of_mem_fixingSubgroup_of_isPrimitiveRoot_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/60cdfa84-3a1c-5cd0-bcd9-67b52fac973e
-- title:
--   Mod p cyclotomic character trivial when ζₚ ∈ L
-- statement:
--   Let $p$ be a prime and let $L$ be an intermediate field of the extension $\overline{\mathbb{Q}}/\mathbb{Q}$, where $\overline{\mathbb{Q}}$ is the chosen algebraic closure `AlgebraicClosure ℚ`. Suppose $\zeta \in \overline{\mathbb{Q}}$ is a primitive $p$-th root of unity and that $\zeta$ lies in $L$. Let $s$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$ belonging to the fixing subgroup of $L$, i.e. $s(x) = x$ for every $x \in L$. The conclusion is that $s$ is killed by the mod $p$ cyclotomic character: the value $\mathrm{cycloChar}\,p\,(s) = 1$ in $(\mathbb{Z}/p)^{\times}$, where `cycloChar p` is the monoid homomorphism from $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ to $(\mathbb{Z}/p)^{\times}$ obtained by viewing an automorphism as a ring isomorphism and applying Mathlib's modular cyclotomic character `modularCyclotomicCharacter` of $\overline{\mathbb{Q}}$ at level $p$, the required hypothesis that the group of $p$-th roots of unity of $\overline{\mathbb{Q}}$ has order exactly $p$ being supplied by `card_rootsOfUnity_eq_self p`.
--
--   This is the standard fact that the mod $p$ cyclotomic character factors through $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}(\zeta_p))$, hence is trivial on the absolute Galois group of any field containing a primitive $p$-th root of unity. It is used in the Kummer-theoretic and Selmer-group computations of the project, for instance in the determination of the dimensions of continuous $H^1$ of the Selmer representation and of its twists, and in the construction of cochains with prescribed cyclotomic level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_cycloChar_eq_one_of_mem_fixingSubgroup_of_isPrimitiveRoot_mem.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation
open scoped Classical

theorem ExtCitation.cycloChar_eq_one_of_mem_fixingSubgroup_of_isPrimitiveRoot_mem
    {p : ℕ} [Fact p.Prime] (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (hζL : ζ ∈ L)
    (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hs : s ∈ L.fixingSubgroup) :
    cycloChar p s = 1 := by sorry
