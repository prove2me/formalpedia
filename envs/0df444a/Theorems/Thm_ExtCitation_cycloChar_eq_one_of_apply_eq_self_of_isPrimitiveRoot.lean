-- Prove2me | Theorems.Thm_ExtCitation_cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot
-- name    : ExtCitation.cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/006408f4-85df-51ce-ac8b-5dabe209ff2b
-- title:
--   Triviality of χₚ on automorphisms fixing ζₚ
-- statement:
--   Let $p$ be a prime, let $g$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, and let $\xi \in \overline{\mathbb{Q}}$ be a primitive $p$-th root of unity, i.e. `IsPrimitiveRoot ξ p` holds. Assume $g(\xi) = \xi$. Then $\mathrm{cycloChar}\,p\,(g) = 1$ in $(\mathbb{Z}/p)^\times$, where `cycloChar p` is the monoid homomorphism from the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$ to $(\mathbb{Z}/p)^\times$ obtained by sending $\sigma$ to the value at the underlying ring automorphism of Mathlib's `modularCyclotomicCharacter` of $\overline{\mathbb{Q}}$ at level $p$ (the fact that $\overline{\mathbb{Q}}$ contains exactly $p$ $p$-th roots of unity being supplied by `card_rootsOfUnity_eq_self p`), multiplicativity being inherited from that character. Thus an automorphism of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ that fixes one primitive $p$-th root of unity has trivial mod-$p$ cyclotomic character; equivalently, $\chi_p$ is trivial on the subgroup fixing $\mathbb{Q}(\zeta_p)$.
--
--   This is the elementary statement that the mod-$p$ cyclotomic character $\chi_p$ of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ restricts trivially to the decomposition of the Galois group fixing $\mathbb{Q}(\zeta_p)$. It is used in the project to show that $\chi_p$ is a character of finite level (smooth) and unramified outside $p$, notably in the construction of dual twists by $\chi_p$ of Galois representations and in the trace identification of the representation attached to an eigensystem on $H^1$ of binary forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot.lean

import Mathlib
import Definitions.Def_ExtCitation_KummerBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ExtCitation

theorem ExtCitation.cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot
    (p : ℕ) [Fact p.Prime] (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    {ξ : AlgebraicClosure ℚ} (hξ : IsPrimitiveRoot ξ p) (hg : g ξ = ξ) :
    cycloChar p g = 1 := by sorry
