-- Prove2me | Theorems.Thm_ExtCitation_exists_inertia_pCharacter_generator
-- name    : ExtCitation.exists_inertia_pCharacter_generator
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/57758eb4-cad3-538a-88d7-c91a740f6455
-- title:
--   A mod p generator of tame inertia at q≠ p
-- statement:
--   Fix a prime $p$ (with the primality instance) and a prime $q$ with $q\ne p$. Write $G_q$ for the group `primeLocalGaloisGroup q` of $\mathbb{Q}_q$-algebra automorphisms of the algebraic closure `PadicAlgCl q`, write $A$ for the valuation subring `primeLocalPlace q` of $\overline{\mathbb{Q}}$ obtained by pulling back $\mathbb{Z}_q$ along the chosen embedding of $\overline{\mathbb{Q}}$ into `PadicAlgCl q`, and write $r=$ `primeLocalToGlobal q` $: G_q\to\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ for restriction of scalars to $\mathbb{Q}$ followed by restriction to the normal subextension $\overline{\mathbb{Q}}$. Put $I'=r^{-1}\bigl(I(A)\bigr)$, where $I(A)\le\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ is the image of the inertia subgroup of $A$ under the inclusion of the decomposition subgroup. Let $\varphi\in G_q$ be such that $r(\varphi)$ lies in the decomposition subgroup of $A$ over $\mathbb{Q}$ and acts on the residue field of $A$ by $x\mapsto x^q$. The conclusion provides $t\in G_q$ together with proofs that $t\in I'$ and $\varphi t\varphi^{-1}\in I'$, such that for every intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is finite-dimensional and Galois over $\mathbb{Q}$, and every homomorphism $\chi\colon I'\to\mathrm{Multiplicative}(\mathbb{Z}/p)$ vanishing on all $i\in I'$ with $r(i)$ in the fixing subgroup of $F$: first, $\chi(t)=1$ forces $\chi=1$; and second, $\chi(\varphi t\varphi^{-1})=\chi(t)^{q}$.
--
--   This is the mod $p$ abelianised shadow of the structure of tame inertia at a prime $q\ne p$: a single element of the pulled-back inertia group detects all $\mathbb{Z}/p$-valued characters of finite level, and Frobenius conjugation multiplies such a character's value by $q$. It is used in the local analysis at auxiliary primes, being cited by [`ModularCurve.exists_mem_inertiaSubgroupIn_forall_jZeroTorsion_pow_smul_eq_imp`](thm.html#ModularCurve.exists_mem_inertiaSubgroupIn_forall_jZeroTorsion_pow_smul_eq_imp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_exists_inertia_pCharacter_generator.lean

import Mathlib
import Definitions.Def_ExtCitation_InertiaKummerCharacter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ExtCitation

theorem ExtCitation.exists_inertia_pCharacter_generator (p : ℕ) [Fact p.Prime] (q : Nat.Primes) (hqp : (q : ℕ) ≠ p)
    (φ : primeLocalGaloisGroup q) (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q) :
    ∃ (t : primeLocalGaloisGroup q)
      (ht : t ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q))
      (hφt : φ * t * φ⁻¹ ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)),
      ∀ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F]
        (χ : ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)) →* Multiplicative (ZMod p)),
        (∀ i : ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)),
          primeLocalToGlobal q (i : primeLocalGaloisGroup q) ∈ F.fixingSubgroup → χ i = 1) →
          (χ ⟨t, ht⟩ = 1 → χ = 1) ∧ χ ⟨φ * t * φ⁻¹, hφt⟩ = χ ⟨t, ht⟩ ^ (q : ℕ) := by sorry
