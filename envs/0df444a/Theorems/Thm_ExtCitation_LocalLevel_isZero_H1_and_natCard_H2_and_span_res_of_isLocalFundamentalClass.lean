-- Prove2me | Theorems.Thm_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
-- name    : ExtCitation.LocalLevel.isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/7fbe2b9e-89d7-5b83-aae0-b7f94ecbe54d
-- title:
--   Local class-formation axioms from a local fundamental class
-- statement:
--   Fix a prime $q$, a finite extension $L$ of $\mathbb{Q}_q$ inside the fixed algebraic closure `PadicAlgCl q`, and a finite group $G$ acting faithfully on $L$ by ring automorphisms, together with a multiplicative action of $G$ on $L^\times$; it is assumed that $G$ fixes the image of $\mathbb{Q}_q$ pointwise (`hG`), that the action on $L^\times$ is the restriction of the action on $L$ (`hcompat`), and that $G$ is solvable. Let $K$ be a further finite extension of $\mathbb{Q}_q$ which is a base for $(L,G)$, i.e. $K\le L$ and an element of $L$ lies in $K$ exactly when it is fixed by all of $G$. Let $u\in H^2(G,L^\times)$ be a local fundamental class, in the sense that for every finite extension $M\supseteq L$, every finite group $H$ acting faithfully on $M$ and on $M^\times$, normal subgroups $N_L,N_n\le H$, an isomorphism $e\colon G\simeq H/N_L$, and elements $\varphi\in H$, $\pi\in (M^\times)$ forming an unramified-overlayer datum — $H$ fixes $\mathbb{Q}_q$, acts on units through $M$, has fixed field $K$ in $M$, $N_L$ has fixed field $L$, the $G$-action on $L$ agrees with the $H$-action through $e$, $\#(H/N_n)=\#G$, the image of $\varphi$ generates $H/N_n$ and acts as the residue-field Frobenius on $N_n$-invariant elements of norm $\le 1$, and $\pi$ is $H$-fixed, lies in $K$, has norm $<1$ and maximal norm among $N_n$-invariant elements of norm $<1$ — and for every morphism $\iota$ of $\mathbb{Z}$-representations from $L^\times$ restricted along $H\to H/N_L\simeq G$ to $M^\times$ which is the identity on underlying field elements, the image of $u$ in $H^2(H,M^\times)$ is the inflation from $H^2(H/N_n,(M^\times)^{N_n})$ of the class of the cyclic carry cocycle attached to $\varphi$ modulo $N_n$ and to $\pi$. The conclusion is the conjunction of three assertions about subgroups $S\le G$: the cohomology $H^1$ of $L^\times$ restricted along $S\hookrightarrow G$ is a zero object; for each finite $S$, $\#H^2(S,L^\times)$ equals the order of $S$; and for each $S$ the image of $u$ under restriction $H^2(G,L^\times)\to H^2(S,L^\times)$ spans $H^2(S,L^\times)$ as a $\mathbb{Z}$-module.
--
--   These are the class-formation axioms for a finite Galois layer of $q$-adic fields: vanishing of $H^1(S,L^\times)$ (Hilbert 90), $\#H^2(S,L^\times)=\#S$, and generation of $H^2(S,L^\times)$ by the restricted fundamental class. The statement is used downstream in the computation of Herbrand quotients and in the construction of the idelic Artin map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass.lean

import Mathlib
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (hsolv : Group.IsSolvable G)
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hK : IsBase q L G K)
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L)ˣ)) (hu : IsLocalFundamentalClass q L G K u) :
    (∀ S : Subgroup G, CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)) 1)) ∧
    (∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)) 2) = Fintype.card S) ∧
    (∀ S : Subgroup G, Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ))) 2).hom u} = ⊤) := by sorry
