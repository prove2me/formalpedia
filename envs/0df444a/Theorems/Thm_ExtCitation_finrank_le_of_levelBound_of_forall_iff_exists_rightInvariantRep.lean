-- Prove2me | Theorems.Thm_ExtCitation_finrank_le_of_levelBound_of_forall_iff_exists_rightInvariantRep
-- name    : ExtCitation.finrank_le_of_levelBound_of_forall_iff_exists_rightInvariantRep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/1c0dfdd8-b129-5ca2-b5d9-8a16e23b2e45
-- title:
--   Locally constant classes bounded by a uniform inflation bound
-- statement:
--   Fix a prime $p$, a prime $q$, and a representation $M$ of $G_q := \mathrm{Aut}_{\mathbb{Q}_q}(\overline{\mathbb{Q}_q})$ (the automorphism group of the chosen algebraic closure `PadicAlgCl q` as a $\mathbb{Q}_q$-algebra) on a finite-dimensional $\mathbb{Z}/p$-vector space; write $r_q : G_q \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ for the homomorphism `primeLocalToGlobal q`, obtained by restricting scalars to $\mathbb{Q}$ and then restricting to the algebraic closure of $\mathbb{Q}$. Let $F_0$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ of finite degree and $b$ a natural number. Assume that for every finite intermediate field $F$ that is normal over $\mathbb{Q}$ and contains $F_0$, the $\mathbb{Z}/p$-dimension of the image of the inflation map $H^1(G_q/U_F, M^{U_F}) \to H^1(G_q, M)$ is at most $b$, where $U_F = r_q^{-1}(\mathrm{Gal}(\overline{\mathbb{Q}}/F))$ is the preimage of the fixing subgroup of $F$. Let $\mathrm{adm}_1$ be a $\mathbb{Z}/p$-submodule of $H^1(G_q, M)$ whose elements are exactly the classes $x$ admitting a $1$-cocycle $c$ with class $x$ such that, for some finite intermediate field $F$, one has $c(gs) = c(g)$ for all $g \in G_q$ and all $s$ with $r_q(s)$ fixing $F$. Then $\dim_{\mathbb{Z}/p} \mathrm{adm}_1 \le b$.
--
--   The submodule $\mathrm{adm}_1$ is the group of locally constant (continuous) classes in $H^1(G_q, M)$, and the statement transports a uniform bound on the finite-level inflation images to a bound on it, the point being that the subgroups $U_F$ form a directed family of normal subgroups of finite index. It is the local Galois-cohomology input used in [`groupCohomology.finrank_continuousClasses_le_invariants_add_dualTwist`](thm.html#groupCohomology.finrank_continuousClasses_le_invariants_add_dualTwist), where the per-level bound is supplied by an invariants-plus-twist computation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_finrank_le_of_levelBound_of_forall_iff_exists_rightInvariantRep.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_ExtCitation_LocalLevelSubgroupsPD
import Definitions.Def_GroupCohomology_LocallyConstantClasses

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory groupCohomology ExtCitation

theorem ExtCitation.finrank_le_of_levelBound_of_forall_iff_exists_rightInvariantRep (p : ℕ) [Fact p.Prime] (q : Nat.Primes) (M : Rep (ZMod p) (primeLocalGaloisGroup q)) [FiniteDimensional (ZMod p) M]
    (F₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F₀]
    (b : ℕ)
    (hlevel : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F → ∀ _ : Normal ℚ F, F₀ ≤ F →
      Module.finrank (ZMod p) (inflationImage M ((F.fixingSubgroup).comap (primeLocalToGlobal q))) ≤ b)
    (adm₁ : Submodule (ZMod p) (H1 M))
    (hadm₁ : ∀ x, x ∈ adm₁ ↔ ∃ c : cocycles₁ M, H1π M c = x ∧
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ g s : primeLocalGaloisGroup q, primeLocalToGlobal q s ∈ F.fixingSubgroup → c (g * s) = c g) :
    Module.finrank (ZMod p) adm₁ ≤ b := by sorry
