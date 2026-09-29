-- Prove2me | Theorems.Thm_ExtCitation_LocalLevel_isLocalFundamentalClass_map_subtype
-- name    : ExtCitation.LocalLevel.isLocalFundamentalClass_map_subtype
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/1829b48f-2fbc-5cee-9c10-10739acab150
-- title:
--   Restriction of the local fundamental class to a subgroup
-- statement:
--   Fix a prime $q$ and work inside a fixed algebraic closure `PadicAlgCl q` of $\mathbb{Q}_q$. Let $L$ be an intermediate field, finite over $\mathbb{Q}_q$, and let $G$ be a finite group acting faithfully on $L$ by semiring automorphisms, with $g\cdot\iota(x)=\iota(x)$ for all $g\in G$ and $x\in\mathbb{Q}_q$ (hypothesis `hG`), together with an action of $G$ on $L^{\times}$ compatible with the action on $L$ under the inclusion $L^{\times}\to L$ (`hcompat`); assume $G$ is solvable. Let $K$ be an intermediate field finite over $\mathbb{Q}_q$ which is a base for $(L,G)$, i.e. $K\le L$ and an element of $L$ lies in $K$ exactly when it is fixed by all of $G$. Let $u\in H^2(G,L^{\times})$ (cohomology of `Rep.ofMulDistribMulAction G (↥L)ˣ`) be a local fundamental class for $(L,G,K)$: for every finite over-layer $M\supseteq L$ with finite group $H$ acting faithfully on $M$, normal subgroups $N_L,N_n\le H$, isomorphism $e:G\simeq H/N_L$, element $\varphi\in H$ and unit $\pi\in M^{\times}$ forming an unramified over-layer datum over $K$, and every morphism $\iota$ from $L^{\times}$ inflated along $H\to H/N_L\simeq G$ to $M^{\times}$ inducing the field inclusion on underlying elements, the pullback of $u$ along $(e^{-1}\circ\mathrm{mk}_{N_L},\iota)$ equals the inflation from $H/N_n$ of the class of the cyclic carry $2$-cocycle `carryFun` attached to the image of $\varphi$ and to $\pi$ viewed in the $N_n$-invariants. Finally let $S\le G$ and let $K_S$ be an intermediate field finite over $\mathbb{Q}_q$ which is a base for $(L,S)$, i.e. $K_S\le L$ and an element of $L$ lies in $K_S$ exactly when it is fixed by every $s\in S$. Then the image of $u$ under the map on $H^2$ induced by the inclusion $S\hookrightarrow G$ and the identity of the restricted representation — the restriction $\mathrm{res}^G_S u\in H^2(S,L^{\times})$ — is a local fundamental class for $(L,S,K_S)$ in the same sense.
--
--   This is the compatibility of local fundamental classes with restriction to a subgroup, $\mathrm{res}^G_S u_{L/K}=u_{L/L^S}$, in the form needed for the local invariant calculus (Serre, Local Fields, Ch. XIII §3). It is used in the Herbrand-quotient computations and in the decomposition of places in the global argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_LocalLevel_isLocalFundamentalClass_map_subtype.lean

import Mathlib
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.isLocalFundamentalClass_map_subtype (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (hsolv : Group.IsSolvable G)
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hK : IsBase q L G K)
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L)ˣ)) (hu : IsLocalFundamentalClass q L G K u)
    (S : Subgroup G) (KS : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] KS] (hKS : IsBase q L (↥S) KS) :
    IsLocalFundamentalClass q L (↥S) KS
      ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ))) 2).hom u) := by sorry
