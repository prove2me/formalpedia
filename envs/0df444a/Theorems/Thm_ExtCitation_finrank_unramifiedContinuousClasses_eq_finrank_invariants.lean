-- Prove2me | Theorems.Thm_ExtCitation_finrank_unramifiedContinuousClasses_eq_finrank_invariants
-- name    : ExtCitation.finrank_unramifiedContinuousClasses_eq_finrank_invariants
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/170f114a-74a6-58e8-a263-79a976c0bffa
-- title:
--   Unramified continuous classes at q have dimension h⁰
-- statement:
--   Fix a prime $p$ and a prime $q$, and let $G_q$ denote `primeLocalGaloisGroup q`, the group of $\mathbb{Q}_q$-algebra automorphisms of the algebraic closure `PadicAlgCl q` of $\mathbb{Q}_q$, together with the monoid homomorphism `primeLocalToGlobal q` $: G_q \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by restricting scalars to $\mathbb{Q}$ and then restricting to the normal subextension $\overline{\mathbb{Q}}$, and with `primeLocalPlace q`, the valuation subring of $\overline{\mathbb{Q}}$ pulled back from $\mathbb{Z}_q$ along the chosen $q$-adic embedding. Let $M$ be a representation of $G_q$ on a finite-dimensional $\mathbb{Z}/p$-vector space which is smooth in the sense that every $m \in M$ is fixed by all $s$ with `primeLocalToGlobal q s` in the fixing subgroup of some finite extension $F/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$. Let $\mathrm{adm}_{\mathrm{ur}}$ be a finite-dimensional $\mathbb{Z}/p$-submodule of $H^1(G_q, M)$ whose elements are exactly the classes of those $1$-cocycles $c$ that are right invariant under the fixing subgroup of some finite $F/\mathbb{Q}$, i.e. $c(gs) = c(g)$ for all $g$ and all such $s$, and that agree on inertia with a coboundary: for some $m \in M$, $c(g) = \rho(g)m - m$ whenever `primeLocalToGlobal q g` lies in the inertia subgroup of `primeLocalPlace q` over $\mathbb{Q}$ (the image of that valuation subring's inertia subgroup inside the Galois group). Then $\dim_{\mathbb{Z}/p} \mathrm{adm}_{\mathrm{ur}} = \dim_{\mathbb{Z}/p} M^{G_q}$.
--
--   This is the unramified local term $h^1_{\mathrm{ur}} = h^0$ of the Greenberg–Wiles product formula at a place $q$, here in a form free of $H^2$ and of local duality pairings, with continuity and the unramified condition expressed directly as conditions on representing cocycles. It feeds the assembly of the unramified local contributions in the Greenberg–Wiles count and the construction of submodules of bounded rank for representations that are unipotent on inertia at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_finrank_unramifiedContinuousClasses_eq_finrank_invariants.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem ExtCitation.finrank_unramifiedContinuousClasses_eq_finrank_invariants
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (M : Rep (ZMod p) (primeLocalGaloisGroup q)) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ F ∧
        ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → M.ρ s m = m)
    (adm_ur : Submodule (ZMod p) (H1 M)) [FiniteDimensional (ZMod p) adm_ur]
    (hadm_ur : ∀ x, x ∈ adm_ur ↔ ∃ c : cocycles₁ M,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ (g s : primeLocalGaloisGroup q),
          primeLocalToGlobal q s ∈ F.fixingSubgroup → c.val (g * s) = c.val g)
      ∧ (∃ m : M, ∀ g : primeLocalGaloisGroup q,
          primeLocalToGlobal q g ∈ (primeLocalPlace q).inertiaSubgroupIn ℚ → c.val g = M.ρ g m - m)
      ∧ (H1π M).hom c = x) :
    finrank (ZMod p) adm_ur = finrank (ZMod p) M.ρ.invariants := by sorry
