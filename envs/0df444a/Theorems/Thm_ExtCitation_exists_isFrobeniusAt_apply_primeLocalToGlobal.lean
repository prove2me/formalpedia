-- Prove2me | Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
-- name    : ExtCitation.exists_isFrobeniusAt_apply_primeLocalToGlobal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/313b5720-07ce-5e52-a71a-218be9640cc9
-- title:
--   Existence of a Frobenius element in the image of G_{ℚ_q}
-- statement:
--   Let $q$ be a prime. Write $G_q$ for the group `primeLocalGaloisGroup q` of automorphisms of the algebraic closure `PadicAlgCl` $q$ of $\mathbb{Q}_q$ over $\mathbb{Q}_q$, and let `primeLocalToGlobal q` be the homomorphism $G_q \to \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by restricting scalars from $\mathbb{Q}_q$ to $\mathbb{Q}$ and then restricting an automorphism of `PadicAlgCl` $q$ to the normal subextension $\overline{\mathbb{Q}}$, the latter being embedded by the chosen map [`padicEmbedding`](def/GaloisRep_CompletionBridge.html#L17) $q$. Let `primeLocalPlace q` be the valuation subring of $\overline{\mathbb{Q}}$ obtained as the preimage of the $q$-adic integers $\mathbb{Z}_q$ inside `PadicAlgCl` $q$ along that embedding. The assertion is that some $\varphi \in G_q$ has the property that $\sigma :=$ `primeLocalToGlobal q` $\varphi$ satisfies `IsFrobeniusAt` for this valuation subring with exponent $q$: namely $\sigma$ lies in the decomposition subgroup of `primeLocalPlace q` over $\mathbb{Q}$, and the induced action of $\sigma$ on the residue field of `primeLocalPlace q` sends every element $x$ to $x^{q}$.
--
--   This is the standard statement that the local Galois group at $q$ surjects onto the Galois group of the residue extension, so that an arithmetic Frobenius at the chosen place of $\overline{\mathbb{Q}}$ above $q$ can be realised as the restriction of a local automorphism. It is used by the local computations at auxiliary primes in the endgame, among them [`ExtCitation.exists_eq_kummerCharacter_pow`](thm.html#ExtCitation.exists_eq_kummerCharacter_pow), [`ExtCitation.finrank_unramifiedContinuousClasses_eq_finrank_invariants`](thm.html#ExtCitation.finrank_unramifiedContinuousClasses_eq_finrank_invariants) and [`ExtCitation.tame_or_descent_of_isSimple`](thm.html#ExtCitation.tame_or_descent_of_isSimple).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ExtCitation

theorem ExtCitation.exists_isFrobeniusAt_apply_primeLocalToGlobal (q : Nat.Primes) :
    ∃ φ : primeLocalGaloisGroup q, (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q := by sorry
