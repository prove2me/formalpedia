-- Prove2me | Theorems.Thm_ExtCitation_LocalLevel_exists_subgroup_units_forall_isMulCocycle
-- name    : ExtCitation.LocalLevel.exists_subgroup_units_forall_isMulCocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/5d571453-b0c7-568c-a174-a1088004d6ec
-- title:
--   A cohomologically trivial open subgroup of the local units
-- statement:
--   Let $q$ be a prime and let $L$ be an intermediate field of $\mathbb{Q}_q \subset \overline{\mathbb{Q}}_q$ that is finite-dimensional over $\mathbb{Q}_q$; write $R =$ `Rw q L` for the pullback along $L \to \overline{\mathbb{Q}}_q$ of the valuation subring attached to the canonical valuation of $\overline{\mathbb{Q}}_q$, i.e. the ring of integers of $L$. Let $G$ be a finite group acting on $L$ by ring automorphisms, faithfully, with $g \cdot \iota(x) = \iota(x)$ for all $g \in G$ and $x \in \mathbb{Q}_q$ (so the action is by $\mathbb{Q}_q$-algebra automorphisms), together with a multiplicative action of $G$ on $L^\times$ by group automorphisms compatible with the action on $L$. Then there are subgroups $U, V \le L^\times$ such that: $U$ consists exactly of those units $u$ with both $u$ and $u^{-1}$ in $R$; $U$ is $G$-stable; $V \le U$ and $V$ is $G$-stable; $V$ has finite index in $U$; for some $n \ge 1$ the image in $L^\times$ of the $n$-th principal unit group of $R$, that is of $\{u \in R^\times : u - 1 \in \mathfrak{m}^n\}$, lies in $V$; every $1$-cocycle $f : G \to L^\times$ with all values in $V$ is $g \mapsto (g \cdot x)/x$ for some $x \in V$; and every $2$-cocycle $f : G \times G \to L^\times$ with all values in $V$ satisfies $f(g,h) = (g \cdot x_h)/x_{gh} \cdot x_g$ for some $1$-cochain $x : G \to L^\times$ with all values in $V$.
--
--   This is the classical lemma that the unit group of a local field contains an open $G$-stable subgroup which is cohomologically trivial, here in an elementwise, logarithm-free form asserting the vanishing of $H^1(G,V)$ and $H^2(G,V)$ directly on cocycles. It feeds the computation of the order of $H^2(G, \mathcal{O}_L^\times)$ for cyclic $G$ and a norm-surjectivity statement for units of a $q$-adic field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_LocalLevel_exists_subgroup_units_forall_isMulCocycle.lean

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_LocalRing_PrincipalUnits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open ExtCitation.LocalLevel IsLocalRing groupCohomology

theorem ExtCitation.LocalLevel.exists_subgroup_units_forall_isMulCocycle (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ] (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L)) :
    ∃ U V : Subgroup (↥L)ˣ,
      (∀ u : (↥L)ˣ, u ∈ U ↔ ((u : L) ∈ Rw q L ∧ ((u⁻¹ : (↥L)ˣ) : L) ∈ Rw q L)) ∧
      (∀ g : G, ∀ u ∈ U, g • u ∈ U) ∧ V ≤ U ∧ (∀ g : G, ∀ v ∈ V, g • v ∈ V) ∧ (V.subgroupOf U).FiniteIndex ∧
      (∃ n : ℕ, 1 ≤ n ∧ ∀ u : (Rw q L)ˣ, u ∈ principalUnits (Rw q L) n →
          Units.map ((Rw q L).subtype : Rw q L →* L) u ∈ V) ∧
      (∀ f : G → (↥L)ˣ, (∀ g, f g ∈ V) → IsMulCocycle₁ f → ∃ x ∈ V, ∀ g, g • x / x = f g) ∧
      (∀ f : G × G → (↥L)ˣ, (∀ p, f p ∈ V) → IsMulCocycle₂ f →
          ∃ x : G → (↥L)ˣ, (∀ g, x g ∈ V) ∧ ∀ g h, g • x h / x (g * h) * x g = f (g, h)) := by sorry
