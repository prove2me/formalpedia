-- Prove2me | Theorems.Thm_ExtCitation_LocalLevel_inv_res_inf_eq_index_smul_inv
-- name    : ExtCitation.LocalLevel.inv_res_inf_eq_index_smul_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/f6550670-3fd4-57dc-beba-e7704c017333
-- title:
--   Restriction multiplies the local invariant by the index [G:S]
-- statement:
--   Let $q$ be a prime and $L$ a finite extension of $\mathbb{Q}_q$ inside a fixed algebraic closure, acted on faithfully by a finite group $G$ through ring automorphisms fixing $\mathbb{Q}_q$ pointwise, together with a multiplicative action of $G$ on $L^\times$ compatible with the action on $L$. Let $K\le L$ and $K'\le L$ be finite subextensions of $\mathbb{Q}_q$ whose elements of $L$ are exactly those fixed by all of $G$, respectively by a subgroup $S\le G$, and let $N\trianglelefteq G$. Assume $\varphi\in G$ has image generating $G/N$, of finite order, and satisfies $\|\varphi\cdot x-x^{\,\#\kappa}\|<1$ for all $N$-invariant $x\in L$ with $\|x\|\le 1$, where $\#\kappa$ is the cardinality of the residue field of the valuation subring $\mathtt{Rw}\,q\,K$ of $K$ (the preimage of the valuation ring of the algebraic closure); assume $\pi\in L^\times$ is $G$-invariant, of norm $<1$, and of maximal norm among $N$-invariant elements of norm $<1$. Assume the analogous data $\psi\in S$, generating $S/(N\cap S)$ with Frobenius congruence relative to the residue field of $\mathtt{Rw}\,q\,K'$, and $\pi'\in L^\times$, $S$-invariant, maximal among $(N\cap S)$-invariant elements of norm $<1$. Let $\mathrm{inv}\colon H^2(G/N,(L^\times)^N)\xrightarrow{\ \sim\ }\mathbb{Z}/\#(G/N)$ and $\mathrm{inv}'\colon H^2\bigl(S/(N\cap S),(L^\times)^{N\cap S}\bigr)\xrightarrow{\ \sim\ }\mathbb{Z}/\#\bigl(S/(N\cap S)\bigr)$ be additive isomorphisms normalised by the carry cocycles: for $a$ in the invariants and $k\in\mathbb{Z}$ with $\|a\|=\|\pi\|^k$ (respectively $\|\pi'\|^k$), the class of the cochain $(g,h)\mapsto a$ if the cyclic logarithms of $g,h$ with respect to the chosen generator sum to at least its order, and $0$ otherwise, has invariant $k$. Finally let $x\in H^2(G/N,(L^\times)^N)$ and $y\in H^2\bigl(S/(N\cap S),(L^\times)^{N\cap S}\bigr)$ satisfy: the restriction along $S\hookrightarrow G$ in degree $2$ of the inflation of $x$ equals the inflation of $y$. Then in $\mathbb{Q}/\mathbb{Z}$, realised as `AddCircle (1 : ℚ)`, one has $\mathrm{inv}'(y)/\#\bigl(S/(N\cap S)\bigr)=[G:S]\cdot \mathrm{inv}(x)/\#(G/N)$, where the invariants are represented by their natural-number values.
--
--   This is the finite-level form, inside a single Galois layer of $q$-adic fields, of the standard compatibility $\mathrm{inv}_{K'}(\mathrm{res}\,\alpha)=[K':K]\,\mathrm{inv}_K(\alpha)$ for the invariant map of local class field theory, the invariant isomorphisms entering as hypotheses through their values on carry cocycles. It is used in the identification of the image of inflation at an unramified level, [`ExtCitation.LocalLevel.range_infNatTrans_eq_of_unramified_level`](thm.html#ExtCitation.LocalLevel.range_infNatTrans_eq_of_unramified_level).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_LocalLevel_inv_res_inf_eq_index_smul_inv.lean

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.inv_res_inf_eq_index_smul_inv (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hKL : K ≤ L)
    (hK : ∀ x : L, (x : PadicAlgCl q) ∈ K ↔ ∀ g : G, g • x = x)
    (S : Subgroup G)
    (K' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K'] (hK'L : K' ≤ L)
    (hK' : ∀ x : L, (x : PadicAlgCl q) ∈ K' ↔ ∀ s ∈ S, s • x = x)
    (N : Subgroup G) [N.Normal]
    (φ : G) (hφN : ∀ g : G ⧸ N, g ∈ Subgroup.zpowers (QuotientGroup.mk' N φ)) (hfinN : IsOfFinOrder (QuotientGroup.mk' N φ))
    (hφ : ∀ x : L, (∀ n ∈ N, n • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
      ‖((φ • x : L) : PadicAlgCl q) - (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K))‖ < 1)
    (π : (↥L)ˣ) (hπG : ∀ g : G, g • π = π) (hπ1 : ‖((π : L) : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : L, (∀ n ∈ N, n • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π : L) : PadicAlgCl q)‖)
    (ψ : S) (hψN : ∀ g : S ⧸ N.subgroupOf S, g ∈ Subgroup.zpowers (QuotientGroup.mk' (N.subgroupOf S) ψ))
    (hfinψ : IsOfFinOrder (QuotientGroup.mk' (N.subgroupOf S) ψ))
    (hψ : ∀ x : L, (∀ n ∈ N ⊓ S, n • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
      ‖(((ψ : G) • x : L) : PadicAlgCl q) - (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K'))‖ < 1)
    (π' : (↥L)ˣ) (hπ'S : ∀ s ∈ S, s • π' = π') (hπ'1 : ‖((π' : L) : PadicAlgCl q)‖ < 1)
    (hπ'max : ∀ y : L, (∀ n ∈ N ⊓ S, n • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π' : L) : PadicAlgCl q)‖)
    (inv : groupCohomology.H2 ((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N) ≃+ ZMod (Nat.card (G ⧸ N)))
    (hinv : ∀ (a : (Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N) (k : ℤ)
        (hc : carryFun (QuotientGroup.mk' N φ) hφN hfinN a ∈ cocycles₂ ((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N)),
        ‖((Additive.toMul (a.1 : Additive (↥L)ˣ) : (↥L)ˣ) : PadicAlgCl q)‖ = ‖((π : L) : PadicAlgCl q)‖ ^ k →
          inv ((H2π ((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N)).hom
              ⟨carryFun (QuotientGroup.mk' N φ) hφN hfinN a, hc⟩) = (k : ZMod (Nat.card (G ⧸ N))))
    (inv' : groupCohomology.H2 ((Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)).quotientToInvariants (N.subgroupOf S)) ≃+
        ZMod (Nat.card (S ⧸ N.subgroupOf S)))
    (hinv' : ∀ (a : (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)).quotientToInvariants (N.subgroupOf S)) (k : ℤ)
        (hc : carryFun (QuotientGroup.mk' (N.subgroupOf S) ψ) hψN hfinψ a ∈
          cocycles₂ ((Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)).quotientToInvariants (N.subgroupOf S))),
        ‖((Additive.toMul (a.1 : Additive (↥L)ˣ) : (↥L)ˣ) : PadicAlgCl q)‖ = ‖((π' : L) : PadicAlgCl q)‖ ^ k →
          inv' ((H2π ((Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)).quotientToInvariants (N.subgroupOf S))).hom
              ⟨carryFun (QuotientGroup.mk' (N.subgroupOf S) ψ) hψN hfinψ a, hc⟩) = (k : ZMod (Nat.card (S ⧸ N.subgroupOf S))))
    (x : groupCohomology.H2 ((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N))
    (y : groupCohomology.H2 ((Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)).quotientToInvariants (N.subgroupOf S)))
    (hxy : (map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ))) 2).hom
        (((infNatTrans ℤ N 2).app (Rep.ofMulDistribMulAction G (↥L)ˣ)).hom x) =
      ((infNatTrans ℤ (N.subgroupOf S) 2).app (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ))).hom y) :
    (((((inv' y).val : ℚ) / (Nat.card (S ⧸ N.subgroupOf S) : ℚ)) : ℚ) : AddCircle (1 : ℚ)) =
      S.index • (((((inv x).val : ℚ) / (Nat.card (G ⧸ N) : ℚ)) : ℚ) : AddCircle (1 : ℚ)) := by sorry
