-- Prove2me | Theorems.Thm_ExtCitation_LocalLevel_range_infNatTrans_eq_of_unramified_level
-- name    : ExtCitation.LocalLevel.range_infNatTrans_eq_of_unramified_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/a384b0a2-62fa-5c64-9f24-5891f32a9878
-- title:
--   Equality of inflation images: solvable layer versus unramified layer
-- statement:
--   Fix a prime $q$ and work inside a fixed algebraic closure `PadicAlgCl q` of $\mathbb{Q}_q$. Let $L$ be an intermediate field of $\mathbb{Q}_q \subseteq$ `PadicAlgCl q` that is finite-dimensional over $\mathbb{Q}_q$, and let $G$ be a finite group acting faithfully on $L$ by ring automorphisms which fix every element of the image of $\mathbb{Q}_q$ (hypothesis `hG`), together with a multiplicative action of $G$ on the unit group $L^\times$ whose underlying map on elements of $L$ agrees with the given action (hypothesis `hcompat`); thus $L^\times$ becomes a representation of $G$ over $\mathbb{Z}$, namely `Rep.ofMulDistribMulAction G (↥L)ˣ`. Let $N_L \trianglelefteq G$ be such that $G/N_L$ is solvable, and let $N_n \trianglelefteq G$ satisfy $\#(G/N_n) = \#(G/N_L)$. Assume given $\pi \in L^\times$ fixed by every element of $G$, with $\|\pi\| < 1$ for the absolute value of `PadicAlgCl q`, and maximal with this property among $N_n$-invariants: every $y \in L$ fixed by all of $N_n$ with $\|y\| < 1$ satisfies $\|y\| \le \|\pi\|$. The conclusion is that the two degree-$2$ inflation maps into $H^2(G, L^\times)$, the components at $L^\times$ of `infNatTrans ℤ NL 2` and of `infNatTrans ℤ Nn 2`, have the same image: $\operatorname{inf}\big(H^2(G/N_L, (L^\times)^{N_L})\big) = \operatorname{inf}\big(H^2(G/N_n, (L^\times)^{N_n})\big)$ as submodules of $H^2(G, L^\times)$.
--
--   This is the local statement that, for a Galois layer of $q$-adic fields, the relative Brauer group of a solvable subextension of degree $n$ coincides with that of the unramified subextension of the same degree, the hypotheses on $\pi$ expressing that the fixed field of $N_n$ is unramified over the fixed field of $G$ by exhibiting a uniformiser already fixed by $G$. It is used in the construction of the local fundamental class, [`ExtCitation.LocalLevel.existsUnique_isLocalFundamentalClass`](thm.html#ExtCitation.LocalLevel.existsUnique_isLocalFundamentalClass).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_LocalLevel_range_infNatTrans_eq_of_unramified_level.lean

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.range_infNatTrans_eq_of_unramified_level (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (NL : Subgroup G) [NL.Normal] (hsolv : Group.IsSolvable (G ⧸ NL))
    (Nn : Subgroup G) [Nn.Normal] (hcard : Nat.card (G ⧸ Nn) = Nat.card (G ⧸ NL))
    (π : (↥L)ˣ) (hπG : ∀ g : G, g • π = π) (hπ1 : ‖((π : L) : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : L, (∀ h ∈ Nn, h • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π : L) : PadicAlgCl q)‖) :
    LinearMap.range (ModuleCat.Hom.hom ((infNatTrans ℤ NL 2).app (Rep.ofMulDistribMulAction G (↥L)ˣ))) =
      LinearMap.range (ModuleCat.Hom.hom ((infNatTrans ℤ Nn 2).app (Rep.ofMulDistribMulAction G (↥L)ˣ))) := by sorry
