-- Prove2me | Theorems.Thm_ExtCitation_LocalLevel_exists_level_frobenius_pow_dvd_and_apply_eq
-- name    : ExtCitation.LocalLevel.exists_level_frobenius_pow_dvd_and_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/b160f8c3-cbe4-5904-9aea-17368939363f
-- title:
--   A finite Galois level with nd ∣ m and φ^m fixing q^{1/n}
-- statement:
--   Let $q$ be a prime and let $G_q$ denote the group `primeLocalGaloisGroup q` of $\mathbb{Q}_q$-algebra automorphisms of the algebraic closure `PadicAlgCl q` of $\mathbb{Q}_q$, with `primeLocalToGlobal q` the homomorphism $r \colon G_q \to \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by restricting scalars to $\mathbb{Q}$ and then restricting to the normal subextension $\overline{\mathbb{Q}}$, and let `primeLocalPlace q` be the valuation subring $A$ of $\overline{\mathbb{Q}}$ pulled back from $\mathbb{Z}_q \subset \mathbb{Q}_q$ along the chosen embedding. Let $\varphi \in G_q$ be such that $r(\varphi)$ lies in the decomposition subgroup of $A$ over $\mathbb{Q}$ and acts on the residue field of $A$ by $x \mapsto x^q$. Let $F_0 \subseteq \overline{\mathbb{Q}}$ be a finite extension of $\mathbb{Q}$, let $n, d \geq 1$ with $q \nmid n$, let $\zeta$ be a primitive $n$-th root of unity in $\overline{\mathbb{Q}}$ and let $\alpha \in \overline{\mathbb{Q}}$ satisfy $\alpha^n = q$. Then there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ containing $F_0$, finite-dimensional and Galois over $\mathbb{Q}$, with $\zeta \in F$ and $\alpha \in F$, such that for every natural number $m$: if $\varphi^m$ lies in the join of the $r$-preimages of the inertia subgroup of $A$ over $\mathbb{Q}$ (taken inside $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ as the image of the inertia subgroup under the inclusion of the decomposition subgroup) and of the fixing subgroup of $F$, then $nd \mid m$ and $r(\varphi^m)$ fixes $\alpha$.
--
--   Since the exponents $m$ with $\varphi^m \in I \vee U_F$ are exactly the multiples of the residue degree of $F$ at the place induced by $q$, the statement produces a finite Galois level $F$ over a prescribed base, containing $\zeta_n$ and an $n$-th root of $q$, whose residue degree at $q$ is divisible by $nd$ and at which the relevant Frobenius powers act trivially on $q^{1/n}$. It is used by [`ExtCitation.exists_tame_generator_at_level_of_dvd`](thm.html#ExtCitation.exists_tame_generator_at_level_of_dvd) in the construction of tame local data at an auxiliary prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_LocalLevel_exists_level_frobenius_pow_dvd_and_apply_eq.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ExtCitation

theorem ExtCitation.LocalLevel.exists_level_frobenius_pow_dvd_and_apply_eq (q : Nat.Primes)
    (φ : primeLocalGaloisGroup q) (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q)
    (F₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F₀]
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hqn : ¬ (q : ℕ) ∣ n)
    {ζ α : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ n) (hα : α ^ n = ((q : ℕ) : AlgebraicClosure ℚ)) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F₀ ≤ F ∧ FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧ ζ ∈ F ∧ α ∈ F ∧
      ∀ m : ℕ, φ ^ m ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)
                        ⊔ (F.fixingSubgroup).comap (primeLocalToGlobal q) →
        n * d ∣ m ∧ primeLocalToGlobal q (φ ^ m) α = α := by sorry
