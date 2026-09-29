-- Prove2me | Theorems.Thm_ExtCitation_exists_frobenius_pow_inv_mul_mem_inertia_sup_level
-- name    : ExtCitation.exists_frobenius_pow_inv_mul_mem_inertia_sup_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/b3df4e0e-99c4-5876-9cfe-71bf1fc62ed4
-- title:
--   Frobenius generates the local group modulo inertia and level
-- statement:
--   Let $q$ be a prime and let $G_q$ denote `primeLocalGaloisGroup q`, the group of $\mathbb{Q}_q$-algebra automorphisms of the chosen algebraic closure `PadicAlgCl q` of $\mathbb{Q}_q$, and let $r =$ `primeLocalToGlobal q` be the homomorphism $G_q \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by restricting scalars to $\mathbb{Q}$ and then restricting to the normal subextension $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Write $A =$ `primeLocalPlace q` for the valuation subring of $\overline{\mathbb{Q}}$ obtained by pulling back the valuation ring of `PadicAlgCl q` along the chosen embedding $\overline{\mathbb{Q}} \to$ `PadicAlgCl q`. Let $\varphi \in G_q$ be such that $r(\varphi)$ is a Frobenius element at $A$ in the sense of `IsFrobeniusAt`: it lies in the decomposition subgroup of $A$ over $\mathbb{Q}$ and acts on the residue field of $A$ by $x \mapsto x^{q}$. Let $F$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is finite-dimensional over $\mathbb{Q}$, and let $g \in G_q$ be arbitrary. Then there is a natural number $n$ with $(\varphi^{n})^{-1} g$ lying in the join of the two subgroups of $G_q$ given by the $r$-preimage of `inertiaSubgroupIn ℚ` of $A$ (the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ inside its decomposition subgroup) and the $r$-preimage of the pointwise fixing subgroup of $F$.
--
--   This is the statement that the image of a Frobenius element topologically generates the local Galois group modulo inertia, here in the concrete form that $\varphi$ generates the quotient of $G_q$ by the join of pulled-back inertia and the pulled-back fixer of any finite level $F$, with only non-negative powers of $\varphi$ needed. It serves as the generation input for the local Galois-cohomology dimension computations at $q$, among them [`ExtCitation.finrank_unramifiedContinuousClasses_eq_finrank_invariants`](thm.html#ExtCitation.finrank_unramifiedContinuousClasses_eq_finrank_invariants), [`ExtCitation.LocalLevel.exists_level_frobenius_pow_dvd_and_apply_eq`](thm.html#ExtCitation.LocalLevel.exists_level_frobenius_pow_dvd_and_apply_eq) and [`ExtCitation.tame_or_descent_of_isSimple`](thm.html#ExtCitation.tame_or_descent_of_isSimple).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_exists_frobenius_pow_inv_mul_mem_inertia_sup_level.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ExtCitation

theorem ExtCitation.exists_frobenius_pow_inv_mul_mem_inertia_sup_level (q : Nat.Primes)
    (φ : primeLocalGaloisGroup q) (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] (g : primeLocalGaloisGroup q) :
    ∃ n : ℕ, (φ ^ n)⁻¹ * g ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)
                        ⊔ (F.fixingSubgroup).comap (primeLocalToGlobal q) := by sorry
