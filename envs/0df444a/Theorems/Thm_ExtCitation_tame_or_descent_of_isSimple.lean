-- Prove2me | Theorems.Thm_ExtCitation_tame_or_descent_of_isSimple
-- name    : ExtCitation.tame_or_descent_of_isSimple
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/da84998f-e80e-5390-a571-000a49f07414
-- title:
--   Tame-or-descent dichotomy for simple smooth mod p local representations
-- statement:
--   Let $p$ be a prime, let $q$ be a prime with $(q:\mathbb{N}) = p$, and let $k$ be a finite field of characteristic $p$. Write $G_q$ for `primeLocalGaloisGroup q`, the group of $\mathbb{Q}_p$-algebra automorphisms of `PadicAlgCl q`, and $r$ for `primeLocalToGlobal q`, the homomorphism sending an automorphism to its restriction of scalars to $\mathbb{Q}$ followed by restriction to $\overline{\mathbb{Q}}$. Let $S \le G_q$ be a subgroup which contains, for some intermediate field $F_0$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ finite over $\mathbb{Q}$, the preimage under $r$ of the subgroup fixing $F_0$ pointwise. Let $N$ be a $k$-linear representation of $S$ which is smooth in the sense that each vector $n \in N$ is fixed by all $s \in S$ whose image under $r$ fixes some intermediate field $F$ finite over $\mathbb{Q}$ pointwise; assume $N$ is finite-dimensional over $k$ of nonzero rank and simple, i.e. every $k$-submodule stable under all $N.\rho\,s$ is $\bot$ or $\top$. Then one of the following holds. Either there is a subgroup $S_0 \le S$ of $G_q$ which again contains the $r$-preimage of the fixing subgroup of some finite intermediate field, whose image in $S$ is normal, such that every $s \in S$ lying in $S_0$ satisfies $N.\rho\,s = 1$ and $\chi_p(r(s)) = 1$, where $\chi_p$ is `cycloChar p`, the mod $p$ cyclotomic character with values in $(\mathbb{Z}/p)^\times$, and such that $p$ does not divide the index of $S_0$ in $S$. Or there is a subgroup $S' \le S$ of $G_q$, again containing the $r$-preimage of the fixing subgroup of some finite intermediate field, normal in $S$ of index exactly $p$, such that the image of $S'$ under $N.\rho$ has strictly smaller cardinality than the image of $S$.
--
--   This is the arithmetic dichotomy that drives the induction in the local Euler–Poincaré characteristic formula for open subgroups of $\mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$: a simple smooth mod $p$ representation either becomes trivial, together with the mod $p$ cyclotomic character, on an open normal subgroup of index prime to $p$, or its image shrinks after passing to an open normal subgroup of index $p$. It is cited by [`groupCohomology.finrank_continuousClasses_eq_invariants_add_continuousH2_add_finrank_of_primeLocal`](thm.html#groupCohomology.finrank_continuousClasses_eq_invariants_add_continuousH2_add_finrank_of_primeLocal), the local Euler-characteristic computation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_tame_or_descent_of_isSimple.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ExtCitation

theorem ExtCitation.tame_or_descent_of_isSimple
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) (hq : (q : ℕ) = p) {k : Type} [Field k] [Finite k] [CharP k p]
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    (N : Rep k S)
    (hsm : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → N.ρ s n = n)
    [FiniteDimensional k N] (hN : Module.finrank k N ≠ 0)
    (hsimple : ∀ W : Submodule k N, (∀ (s : S) (v : N), v ∈ W → N.ρ s v ∈ W) → W = ⊥ ∨ W = ⊤) :
    (∃ S₀ : Subgroup (primeLocalGaloisGroup q), S₀ ≤ S ∧
        (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
          F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S₀) ∧
        (S₀.subgroupOf S).Normal ∧
        (∀ s : S, (s : primeLocalGaloisGroup q) ∈ S₀ → N.ρ s = 1 ∧ cycloChar p (primeLocalToGlobal q s) = 1) ∧
        ¬ p ∣ (S₀.subgroupOf S).index) ∨
    (∃ (S' : Subgroup (primeLocalGaloisGroup q)) (hle : S' ≤ S),
        (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
          F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S') ∧
        (S'.subgroupOf S).Normal ∧ (S'.subgroupOf S).index = p ∧
        Nat.card (MonoidHom.mrange (N.ρ.comp (Subgroup.inclusion hle)))
          < Nat.card (MonoidHom.mrange N.ρ)) := by sorry
