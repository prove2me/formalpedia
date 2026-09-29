-- Prove2me | Theorems.Thm_ExtCitation_LocalLevel_exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun
-- name    : ExtCitation.LocalLevel.exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/389c4d6a-6a37-5edc-ae24-6627d0af05fe
-- title:
--   Invariant isomorphism for H² of an unramified sub-layer
-- statement:
--   Let $q$ be a prime, let $L$ be an intermediate field between $\mathbb{Q}_q$ and a fixed algebraic closure $\mathrm{PadicAlgCl}\,q$ with $L/\mathbb{Q}_q$ finite, and let $G$ be a finite group acting faithfully on $L$ by ring automorphisms, fixing the image of $\mathbb{Q}_q$ pointwise, together with a multiplicative action of $G$ on $L^\times$ compatible with the action on $L$. Let $N\trianglelefteq G$, let $\varphi\in G$ be such that its image $\bar\varphi$ in $G/N$ has finite order and every element of $G/N$ lies in the cyclic group it generates, and let $\pi\in L^\times$ be fixed by all of $G$, satisfy $\|\pi\|<1$, and be of maximal norm among the elements $y\in L$ fixed by $N$ with $\|y\|<1$. Then there is an isomorphism of additive groups $\mathrm{inv}$ from $H^2$ of the $G/N$-representation of $N$-invariants of $\mathrm{Additive}\,L^\times$ onto $\mathbb{Z}/\mathrm{card}(G/N)$ with the following normalisation: for every element $a$ of that representation, every $k\in\mathbb{Z}$, and every proof that the carry cochain of $a$ along $\bar\varphi$ — the $2$-cochain sending $(g,h)$ to $a$ when the sum of the discrete logarithms of $g$ and $h$ to base $\bar\varphi$, taken in $\{0,\dots,\mathrm{ord}(\bar\varphi)-1\}$, is at least $\mathrm{ord}(\bar\varphi)$, and to $0$ otherwise — is a $2$-cocycle, if the unit underlying $a$ has norm $\|\pi\|^k$ then $\mathrm{inv}$ of the cohomology class of that cocycle is $k \bmod \mathrm{card}(G/N)$.
--
--   This is the invariant map of local class field theory for an unramified sub-layer, realised inside a single ambient layer $L/L^G$: the hypothesis on $\pi$ says that a $G$-fixed uniformiser of $L^N$ exists, and the normalisation identifies $H^2(G/N,(L^\times)^N)$ with $\mathbb{Z}/[G:N]$ through the carry cocycles of the cyclic quotient. It is used to compute inflation maps and to characterise local fundamental classes, for instance in [`ExtCitation.LocalLevel.infNatTrans_carryFun_eq_mul_natCard_smul_of_forall_norm_mem`](thm.html#ExtCitation.LocalLevel.infNatTrans_carryFun_eq_mul_natCard_smul_of_forall_norm_mem) and in the `isLocalFundamentalClass` lemmas.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_LocalLevel_exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun.lean

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.exists_addEquiv_H2_quotientToInvariants_units_zmod_forall_carryFun (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (N : Subgroup G) [N.Normal]
    (φ : G) (hφN : ∀ g : G ⧸ N, g ∈ Subgroup.zpowers (QuotientGroup.mk' N φ)) (hfinN : IsOfFinOrder (QuotientGroup.mk' N φ))
    (π : (↥L)ˣ) (hπG : ∀ g : G, g • π = π) (hπ1 : ‖((π : L) : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : L, (∀ n ∈ N, n • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π : L) : PadicAlgCl q)‖) :
    ∃ inv : groupCohomology.H2 ((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N) ≃+ ZMod (Nat.card (G ⧸ N)),
      ∀ (a : (Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N) (k : ℤ)
        (hc : carryFun (QuotientGroup.mk' N φ) hφN hfinN a ∈ cocycles₂ ((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N)),
        ‖((Additive.toMul (a.1 : Additive (↥L)ˣ) : (↥L)ˣ) : PadicAlgCl q)‖ = ‖((π : L) : PadicAlgCl q)‖ ^ k →
          inv ((H2π ((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N)).hom
              ⟨carryFun (QuotientGroup.mk' N φ) hφN hfinN a, hc⟩) = (k : ZMod (Nat.card (G ⧸ N))) := by sorry
