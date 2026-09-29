-- Prove2me | Theorems.Thm_ExtCitation_cycloChar_complexConjugation_eq_neg_one
-- name    : ExtCitation.cycloChar_complexConjugation_eq_neg_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/f282c2e8-80ce-540c-bbc7-f00f4a08048f
-- title:
--   Mod-p cyclotomic character of complex conjugation is -1
-- statement:
--   Let $p$ be a prime. Consider the homomorphism `cycloChar p` from the group $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q}) = (\overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q})$ of $\mathbb Q$-algebra automorphisms of the algebraic closure $\overline{\mathbb Q}$ to $(\mathbb Z/p)^\times$, defined by sending $\sigma$ to the value at $\sigma$, viewed as a ring automorphism, of Mathlib's `modularCyclotomicCharacter` for $\overline{\mathbb Q}$ relative to the fact that the group of $p$-th roots of unity of $\overline{\mathbb Q}$ has cardinality $p$; thus $\sigma(t) = t^{\,\mathrm{cycloChar}\,p\,\sigma}$ for every $p$-th root of unity $t$, the exponent being read in $\mathbb Z/p$. Let [`complexConjugation`](def/GaloisRep_ComplexConjugation.html#L30) be the automorphism of $\overline{\mathbb Q}$ obtained by restricting, via `AlgEquiv.restrictNormalHom`, the $\mathbb Q$-algebra automorphism of $\mathbb C$ given by complex conjugation (`starRingAut`, which fixes the rationals). The assertion is the equality $\mathrm{cycloChar}\,p\,(\text{complexConjugation}) = -1$ in $(\mathbb Z/p)^\times$. (For $p = 2$ this is the trivial element.)
--
--   This is the standard computation that complex conjugation acts on $p$-th roots of unity by inversion, i.e. that the mod-$p$ cyclotomic character of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ is $-1$ at the archimedean place. It is used in the cohomological bookkeeping for Galois representations, in [`groupCohomology.finrank_invariants_archimedean_add_dualTwist_add_H1_eq`](thm.html#groupCohomology.finrank_invariants_archimedean_add_dualTwist_add_H1_eq) and [`groupCohomology.finsum_finrank_invariants_twist_inv_add_eq_index_mul`](thm.html#groupCohomology.finsum_finrank_invariants_twist_inv_add_eq_index_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_cycloChar_complexConjugation_eq_neg_one.lean

import Mathlib
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GaloisRep_ComplexConjugation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ExtCitation

theorem ExtCitation.cycloChar_complexConjugation_eq_neg_one
    (p : ℕ) [Fact p.Prime] :
    cycloChar p complexConjugation = -1 := by sorry
