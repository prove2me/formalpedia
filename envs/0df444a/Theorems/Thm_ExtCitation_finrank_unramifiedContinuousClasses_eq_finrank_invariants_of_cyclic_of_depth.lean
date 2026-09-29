-- Prove2me | Theorems.Thm_ExtCitation_finrank_unramifiedContinuousClasses_eq_finrank_invariants_of_cyclic_of_depth
-- name    : ExtCitation.finrank_unramifiedContinuousClasses_eq_finrank_invariants_of_cyclic_of_depth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/3f01ce4d-1a25-53b6-9fd4-7e5e8f04a9dc
-- title:
--   Unramified continuous classes have dimension h⁰ at q
-- statement:
--   Fix a prime $p$ (with $\mathbb{Z}/p$ a field) and a prime $q$, and let $G_q$ denote `primeLocalGaloisGroup q`, the group of $\mathbb{Q}_q$-algebra automorphisms of the algebraic closure `PadicAlgCl q`, with `primeLocalToGlobal q` the homomorphism $r_q \colon G_q \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ given by restriction of scalars to $\mathbb{Q}$ followed by restriction to the normal subextension $\overline{\mathbb{Q}}$, and `primeLocalPlace q` the valuation subring of $\overline{\mathbb{Q}}$ obtained by pulling back $\mathbb{Z}_q$ along the chosen embedding; write $I \le \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ for the image of the inertia subgroup of that valuation subring under the inclusion of its decomposition subgroup. Let $M$ be a finite-dimensional $\mathbb{Z}/p$-linear representation of $G_q$ which is smooth in the sense that each $m \in M$ is fixed by every $s$ with $r_q(s)$ in the fixing subgroup of some intermediate field $F/\mathbb{Q}$ of finite degree. Let $\varphi \in G_q$ be such that (cyclicity) for every finite normal $F/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ the quotient of $G_q$ by $r_q^{-1}(I) \sqcup r_q^{-1}(\mathrm{Gal}(\overline{\mathbb{Q}}/F))$ consists of integral powers of the class of $\varphi$, and (depth) above any finite $F_0$ and for any $n > 0$ there is a finite normal $F \supseteq F_0$ with $\varphi^{\,j}$ in that join only if $n \mid j$. Let $\mathrm{adm}_{\mathrm{ur}}$ be a finite-dimensional $\mathbb{Z}/p$-submodule of $H^1(G_q, M)$ whose elements are exactly the classes of $1$-cocycles $c$ that are right-invariant under some finite level ($c(gs) = c(g)$ whenever $r_q(s)$ fixes some finite $F$) and satisfy $c(g) = \rho(g)m - m$ on $\{g : r_q(g) \in I\}$ for some $m \in M$. Then $\dim_{\mathbb{Z}/p} \mathrm{adm}_{\mathrm{ur}} = \dim_{\mathbb{Z}/p} M^{G_q}$.
--
--   This is the unramified local term $h^1_{\mathrm{ur}} = h^0$ of the Greenberg–Wiles local computation at a place $q \neq p$, stated for the carrier local Galois group with the continuity and unramifiedness conditions written out as conditions on representing cocycles, and conditional on cyclicity of the unramified finite-level quotients together with a depth condition on $\varphi$. It feeds the unconditional form [`ExtCitation.finrank_unramifiedContinuousClasses_eq_finrank_invariants`](thm.html#ExtCitation.finrank_unramifiedContinuousClasses_eq_finrank_invariants), which supplies one row of the local input to the Selmer-group dimension count.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_finrank_unramifiedContinuousClasses_eq_finrank_invariants_of_cyclic_of_depth.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ExtCitation_LocalLevelSubgroupsPD

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem ExtCitation.finrank_unramifiedContinuousClasses_eq_finrank_invariants_of_cyclic_of_depth
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (M : Rep (ZMod p) (primeLocalGaloisGroup q)) [FiniteDimensional (ZMod p) M]

    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ F ∧
        ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → M.ρ s m = m)

    (φ : primeLocalGaloisGroup q)
    (hcyc : ∀ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [Normal ℚ F],
      ∀ x : primeLocalGaloisGroup q ⧸
          ((((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)) ⊔
            ((F.fixingSubgroup).comap (primeLocalToGlobal q))),
        x ∈ Subgroup.zpowers (QuotientGroup.mk φ :  primeLocalGaloisGroup q ⧸
          ((((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)) ⊔
            ((F.fixingSubgroup).comap (primeLocalToGlobal q)))))

    (hdepth : ∀ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ → ∀ n : ℕ, 0 < n →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ Normal ℚ F ∧ F₀ ≤ F ∧
        ∀ j : ℕ, φ ^ j ∈ ((((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)) ⊔
            ((F.fixingSubgroup).comap (primeLocalToGlobal q))) → n ∣ j)

    (adm_ur : Submodule (ZMod p) (H1 M)) [FiniteDimensional (ZMod p) adm_ur]
    (hadm_ur : ∀ x, x ∈ adm_ur ↔ ∃ c : cocycles₁ M,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ (g s : primeLocalGaloisGroup q),
          primeLocalToGlobal q s ∈ F.fixingSubgroup → c.val (g * s) = c.val g)
      ∧ (∃ m : M, ∀ g : primeLocalGaloisGroup q,
          primeLocalToGlobal q g ∈ (primeLocalPlace q).inertiaSubgroupIn ℚ → c.val g = M.ρ g m - m)
      ∧ (H1π M).hom c = x) :
    finrank (ZMod p) adm_ur = finrank (ZMod p) M.ρ.invariants := by sorry
