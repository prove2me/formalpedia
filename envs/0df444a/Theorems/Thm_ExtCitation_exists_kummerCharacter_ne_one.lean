-- Prove2me | Theorems.Thm_ExtCitation_exists_kummerCharacter_ne_one
-- name    : ExtCitation.exists_kummerCharacter_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/bcd3d015-de07-5f2c-b1f4-3ed2d3c907d3
-- title:
--   Nontriviality of the Kummer character on inertia at q
-- statement:
--   Let $p$ be a natural number carrying the hypothesis that it is prime, let $q$ be a prime, and assume $q \neq p$ as natural numbers. Consider the group $\mathrm{Gal}(\overline{\mathbb{Q}_q}/\mathbb{Q}_q)$, written `primeLocalGaloisGroup q`, together with the homomorphism `primeLocalToGlobal q` to $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by restricting scalars to $\mathbb{Q}$ and then restricting to the normal subextension $\overline{\mathbb{Q}}$; let `primeLocalPlace q` be the valuation subring of $\overline{\mathbb{Q}}$ pulled back from the $q$-adic integers along a fixed embedding $\overline{\mathbb{Q}} \to \overline{\mathbb{Q}_q}$, and let its inertia subgroup in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ be the image of the inertia subgroup under the inclusion of the decomposition subgroup. The assertion is that in the subgroup of $\mathrm{Gal}(\overline{\mathbb{Q}_q}/\mathbb{Q}_q)$ consisting of those elements whose image under `primeLocalToGlobal q` lies in that inertia subgroup there is an element $t$ with `kummerCharacter p q hqp t ≠ 1`. Here `kummerCharacter p q hqp` sends $\sigma$ to the additive-to-multiplicative image of the exponent $n \in \mathbb{Z}/p$ determined by $(\mathrm{primeLocalToGlobal}\,q\,\sigma)(\alpha) = \zeta^{n}\alpha$, where $\alpha$ is the chosen $p$-th root of $q$ in $\overline{\mathbb{Q}}$ and $\zeta$ the chosen primitive $p$-th root of unity. Thus some element of inertia at $q$ moves $\alpha$.
--
--   This records that $\mathbb{Q}_q(q^{1/p})/\mathbb{Q}_q$ is ramified for $q \neq p$, so the Kummer character attached to $q^{1/p}$ is nontrivial on inertia at $q$; it is the input that makes a generator of the $p$-part of the inertia character meaningful. It is used by [`ExtCitation.exists_eq_kummerCharacter_pow`](thm.html#ExtCitation.exists_eq_kummerCharacter_pow) and [`ExtCitation.exists_inertia_pCharacter_generator`](thm.html#ExtCitation.exists_inertia_pCharacter_generator).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_exists_kummerCharacter_ne_one.lean

import Mathlib
import Definitions.Def_ExtCitation_InertiaKummerCharacter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ExtCitation

theorem ExtCitation.exists_kummerCharacter_ne_one (p : ℕ) [Fact p.Prime] (q : Nat.Primes) (hqp : (q : ℕ) ≠ p) :
    ∃ t : ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)), kummerCharacter p q hqp t ≠ 1 := by sorry
