-- Prove2me | Theorems.Thm_ExtCitation_LocalLevel_exists_fixedLevel_quotientToInvariants_iso
-- name    : ExtCitation.LocalLevel.exists_fixedLevel_quotientToInvariants_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/e1f06eff-5ebc-53bd-8777-43394eda826f
-- title:
--   Fixed level L^N and N-invariant units as a G/N-representation
-- statement:
--   Fix a prime $q$ and a finite extension $L$ of $\mathbb{Q}_q$ realised as an intermediate field of a fixed algebraic closure $\mathbb{Q}_q \subset$ `PadicAlgCl q`. Let $G$ be a finite group acting on $L$ by ring and monoid automorphisms (a `MulSemiringAction`), faithfully, and fixing the image of $\mathbb{Q}_q$ pointwise, i.e. $g \cdot \iota(x) = \iota(x)$ for all $g \in G$, $x \in \mathbb{Q}_q$, where $\iota$ is the structure map; let $G$ also act on the unit group $L^\times$ by group automorphisms (a `MulDistribMulAction`) compatibly, in the sense that the inclusion $L^\times \to L$ is $G$-equivariant. Let $N$ be a normal subgroup of $G$. The assertion is that there exists an intermediate field $L'$ of $\mathbb{Q}_q \subset$ `PadicAlgCl q`, finite over $\mathbb{Q}_q$, carrying a faithful $G/N$-action by ring automorphisms and a compatible $G/N$-action by group automorphisms on $(L')^\times$, again fixing the image of $\mathbb{Q}_q$ pointwise and again compatible with $(L')^\times \hookrightarrow L'$, such that the $G/N$-representation of $N$-invariants `(Rep.ofMulDistribMulAction G Lˣ).quotientToInvariants N` is isomorphic to `Rep.ofMulDistribMulAction (G ⧸ N) L'ˣ`. No formula for $L'$ is asserted in the conclusion, only its existence together with all of this data.
--
--   This is the packaging step for the dévissage of $H^2(\mathrm{Gal}(L/K), L^\times)$ along a normal series: it produces, for the quotient group $G/N$, a level $L'$ (the fixed field $L^N$, so that the Galois correspondence gives faithfulness) carrying exactly the data required of a level, and identifies the $N$-invariant units of $L$ with the units of $L'$ as $G/N$-representations. It is used in the computation of $H^2$ of unit groups for solvable $G$ and in the identification of the range of the inflation map at an unramified level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_LocalLevel_exists_fixedLevel_quotientToInvariants_iso.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open groupCohomology

theorem ExtCitation.LocalLevel.exists_fixedLevel_quotientToInvariants_iso (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (N : Subgroup G) [N.Normal] :
    ∃ (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] L')
      (_ : MulSemiringAction (G ⧸ N) L') (_ : FaithfulSMul (G ⧸ N) L')
      (_ : MulDistribMulAction (G ⧸ N) (↥L')ˣ),
      (∀ (g : G ⧸ N) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x) ∧
      (∀ (g : G ⧸ N) (u : (↥L')ˣ), ((g • u : (↥L')ˣ) : L') = g • (u : L')) ∧
      Nonempty ((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N ≅
        Rep.ofMulDistribMulAction (G ⧸ N) (↥L')ˣ) := by sorry
