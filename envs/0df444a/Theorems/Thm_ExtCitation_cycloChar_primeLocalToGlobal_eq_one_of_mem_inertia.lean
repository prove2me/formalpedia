-- Prove2me | Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
-- name    : ExtCitation.cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/9811d645-845a-5261-92bf-52ab28a032f4
-- title:
--   Triviality of χₚ on inertia at q≠ p
-- statement:
--   Let $p$ be a prime (as a `Fact`), let $q$ be a prime, and assume $q \neq p$ as natural numbers. Let $\sigma$ be an element of `primeLocalGaloisGroup q`, that is, a $\mathbb{Q}_q$-algebra automorphism of the algebraic closure `PadicAlgCl q` of $\mathbb{Q}_q$, and write $r_q(\sigma) =$ `primeLocalToGlobal q σ` for its image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, obtained by restricting scalars to $\mathbb{Q}$ and then applying `AlgEquiv.restrictNormalHom` to the normal subextension $\overline{\mathbb{Q}} \subseteq$ `PadicAlgCl q`. Assume that $\sigma$ lies in the pullback along $r_q$ of `inertiaSubgroupIn ℚ` of the valuation subring `primeLocalPlace q` of $\overline{\mathbb{Q}}$ — the latter being the preimage of the $q$-adic integers under the embedding [`padicEmbedding q`](def/GaloisRep_CompletionBridge.html#L17) of $\overline{\mathbb{Q}}$ into `PadicAlgCl q`, and `inertiaSubgroupIn ℚ` being the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of that valuation subring under the inclusion of its decomposition subgroup. The conclusion is that `cycloChar p (primeLocalToGlobal q σ) = 1` in $(\mathbb{Z}/p)^{\times}$, where `cycloChar p` is the monoid homomorphism on $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ given by the mod $p$ cyclotomic character `modularCyclotomicCharacter` of $\overline{\mathbb{Q}}$.
--
--   This is the assertion that $\mathbb{F}_p(1)$ is unramified at every prime $q \neq p$, i.e. $\chi_p|_{I_q} = 1$. It is used in the comparison of continuous cohomology with invariants and the Cartier-dual twist at primes away from $p$, being cited by [`groupCohomology.finrank_continuousClasses_le_invariants_add_dualTwist`](thm.html#groupCohomology.finrank_continuousClasses_le_invariants_add_dualTwist) and [`groupCohomology.invariants_add_dualTwist_le_finrank_continuousClasses`](thm.html#groupCohomology.invariants_add_dualTwist_le_finrank_continuousClasses).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem ExtCitation.cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
    (p : ℕ) [Fact p.Prime] (q : Nat.Primes) (hqp : (q : ℕ) ≠ p)
    {σ : primeLocalGaloisGroup q}
    (hσ : σ ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)) :
    cycloChar p (primeLocalToGlobal q σ) = 1 := by sorry
