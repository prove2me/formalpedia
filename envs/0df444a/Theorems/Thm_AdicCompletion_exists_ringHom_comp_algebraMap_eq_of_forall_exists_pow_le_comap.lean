-- Prove2me | Theorems.Thm_AdicCompletion_exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap
-- name    : AdicCompletion.exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/29fb5433-6128-539e-ab68-70c501c94a4b
-- title:
--   Extension of a ring map to the adic completion
-- statement:
--   Let $B$ be a commutative ring and $\mathfrak m \subseteq B$ an ideal, let $S$ be a commutative ring and $J \subseteq S$ an ideal such that $S$ is $J$-adically complete in Mathlib's sense (`IsAdicComplete J S`, i.e. $S$ is both Hausdorff and complete for the $J$-adic filtration), and let $\mathrm{ev} : B \to S$ be a ring homomorphism. Assume the continuity condition that for every $k \in \mathbb N$ there exists $n \in \mathbb N$ with $\mathfrak m^{n} \le (J^{k}).\mathrm{comap}\,\mathrm{ev}$, that is, $\mathrm{ev}(\mathfrak m^{n}) \subseteq J^{k}$. Then there exists a ring homomorphism $\psi : \widehat{B}_{\mathfrak m} \to S$ from the $\mathfrak m$-adic completion `AdicCompletion 𝔪 B` of $B$ whose composition with the canonical map $B \to \widehat{B}_{\mathfrak m}$ (the `algebraMap`) equals $\mathrm{ev}$. Only existence is asserted: no uniqueness, continuity or further property of $\psi$ is claimed.
--
--   This is the universal property of adic completion in the form usually needed in practice: an adically continuous homomorphism into an adically complete ring factors through the completion of the source. It is used in the project to produce homomorphisms out of completed local rings, for instance when passing from a local ring with finite residue field to a discrete valuation ring, when identifying a completion with an `AdjoinRoot` in the étale case, and in the bookkeeping of prolongations of places on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdicCompletion_exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Valued AdicCompletion in

theorem AdicCompletion.exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap
    {B : Type*} [CommRing B] (𝔪 : Ideal B) {S : Type*} [CommRing S] (J : Ideal S) [IsAdicComplete J S] (ev : B →+* S)
    (hcont : ∀ k : ℕ, ∃ n : ℕ, 𝔪 ^ n ≤ (J ^ k).comap ev) :
    ∃ ψ : AdicCompletion 𝔪 B →+* S, ψ.comp (algebraMap B (AdicCompletion 𝔪 B)) = ev := by sorry
