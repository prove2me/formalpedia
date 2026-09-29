-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_chartSupported_repr_of_mem_invariants_rationalTateModule_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- name    : AlgebraicCurve.exists_chartSupported_repr_of_mem_invariants_rationalTateModule_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/83341685-1260-5d1e-b186-88ede8ae6875
-- title:
--   Chart-supported degree-zero representatives of inertia-invariant Tate vectors
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A \subseteq L$ a valuation subring, and $\pi \in A$ a nonzero element of the maximal ideal; assume the value group is cofinal in the sense that for every $x \in L^{\times}$ and every $y$ in the maximal ideal of $A$ some power $y^{n}$ has valuation at most that of $x$. Let $F$ be a field extension of $L$, and let $n, m$ be natural numbers. For $i : \mathrm{Fin}\,n$ let $\bar F_i$ be a field over the residue field of $A$, all of whose places are rational (the structure map to the residue field of a place is surjective), and let $C_i$ be a `ComponentChart`: a valuation subring of $F$ containing the elements of $A$ and no more from $L$, with a surjective residue homomorphism onto $\bar F_i$ whose kernel is the maximal ideal, a set $(C_i).\mathrm{dom}$ of places of $F/L$, a finite set of nodes among places of $\bar F_i$, and a map $(C_i).\mathrm{placeMap}$ on places subject to the compatibility axioms of that structure; all places in $(C_i).\mathrm{dom}$ are assumed rational. Let $An, An' : \mathrm{Fin}\,m \to \mathrm{Annulus}\,A\,F$ with source and target maps $\mathrm{src}, \mathrm{tgt} : \mathrm{Fin}\,m \to \mathrm{Fin}\,n$, nodes $x_s(e)$ of $\bar F_{\mathrm{src}(e)}$ and $x_t(e)$ of $\bar F_{\mathrm{tgt}(e)}$, and widths $w : \mathrm{Fin}\,m \to \mathbb{N}$, subject to: $An'(e)$ and $An(e)$ have the same domain and the same modulus, that modulus is nonzero in $L$ and the product of the two parameters is its image in $F$; each modulus is a unit times $\pi^{w(e)}$; $An(e)$ is attached to $C_{\mathrm{src}(e)}$ at $x_s(e)$ and $An'(e)$ to $C_{\mathrm{tgt}(e)}$ at $x_t(e)$ in the sense of `Annulus.IsAttached`; every node of every chart is an endpoint of an annulus, and the map from $\mathrm{Fin}\,m \oplus \mathrm{Fin}\,m$ sending an edge to its source or target node is injective on the fibres over nodes; every place of $F/L$ lies either in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain; for each $i$ and each non-node place $Q$ of $\bar F_i$ there is $T$ in the integers of $C_i$ whose residue is nonzero with $\mathrm{ord}_Q = 1$, lying in the valuation subring of every place of $(C_i).\mathrm{dom}$ over $Q$ with value in the maximal ideal of $A$, and such that every $c$ in the maximal ideal of $A$ is the value of $T$ at a unique place of $(C_i).\mathrm{dom}$ over $Q$; and the genus relation $g(F/L) + n = \sum_i g(\bar F_i/\text{residue field}) + m + 1$, where $g$ is $\dim H^1(0)$. Assume $F/L$ is a curve (principal divisors of degree zero exist, residue fields are finite over $L$, and $\Omega_{F/L}$ is free of rank one) and essentially of finite type, and likewise for each $\bar F_i$. Let $S$ be a set of semilinear automorphisms of $F$ over $L$ (pairs consisting of a ring automorphism of $F$ and one of $L$ compatible with the structure map) such that each $s \in S$ stabilises $A$, fixes $\pi$, induces the identity on the residue field of $A$, preserves every chart domain and every annulus domain, fixes the parameter of every $An(e)$ and every $An'(e)$, preserves the integers of each chart compatibly with its residue map, and commutes with each $(C_i).\mathrm{placeMap}$; assume moreover that every ring automorphism of $L$ stabilising $A$, fixing $\pi$ and inducing the identity on the residue field of $A$ is the base automorphism of some element of $S$. Let $\ell$ be a prime whose image in the residue field of $A$ is a unit, assume some $s \in S$ moves some $\ell$-th root of $\pi$, assume the rational $\ell$-adic Tate module $\mathbb{Q}_\ell \otimes_{\mathbb{Z}_\ell} T_\ell(\mathrm{Pic}^0(F/L))$ is finite-dimensional over $\mathbb{Q}_\ell$, and let $M$ be a semistable model over $A$ of the given covering data together with a descent datum for $M$. Then for every vector $v$ in the intersection over $s \in S$ of the kernels of $\mathrm{rationalGaloisRep}(\ell)(s) - 1$ on the rational Tate module, every $x$ in the integral Tate module $T_\ell(\mathrm{Pic}^0(F/L))$ with $v = 1 \otimes x$, and every $k \in \mathbb{N}$, there are a divisor $D$ of $F/L$ of degree zero and divisors $D_i$ ($i : \mathrm{Fin}\,n$) such that the class of $D$ in $\mathrm{Pic}^0$ equals the $k$-th component $\mathrm{proj}_k(x)$, $D = \sum_i D_i$, the support of each $D_i$ is contained in $(C_i).\mathrm{dom}$, and each $D_i$ has degree zero.
--
--   This is the representability step for inertia-invariant $\ell$-adic Tate vectors on a curve with semistable reduction: each finite-level class $\mathrm{proj}_k(x)$ of such a vector is realised by a divisor which splits as a sum of degree-zero divisors supported on the individual components of the reduction, i.e. lies in the identity component of the Picard scheme of the model. It feeds the construction of the reduction map on the invariants and the resulting dimension bound, and is cited by the lemmas on the kernel of that reduction map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_chartSupported_repr_of_mem_invariants_rationalTateModule_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open scoped TensorProduct

theorem
    AlgebraicCurve.exists_chartSupported_repr_of_mem_invariants_rationalTateModule_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : Fin m → Annulus A F) (src tgt : Fin m → Fin n)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : Fin m → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (hdisc : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hgenus : genusFF L F + n = (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + m + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (S : Set (SemilinearAut L F))
    (hS : ∀ s ∈ S, (∀ a : L, a ∈ A ↔ SemilinearAut.baseAut s a ∈ A) ∧ SemilinearAut.baseAut s (π : L) = (π : L) ∧
      (∀ (a : A) (h : SemilinearAut.baseAut s (a : L) ∈ A),
        IsLocalRing.residue A ⟨SemilinearAut.baseAut s (a : L), h⟩ = IsLocalRing.residue A a) ∧
      (∀ i, ∀ P ∈ (C i).dom, s • P ∈ (C i).dom) ∧ (∀ e, ∀ P ∈ (An e).dom, s • P ∈ (An e).dom) ∧
      (∀ e, s • (An e).param = (An e).param) ∧ (∀ e, s • (An' e).param = (An' e).param) ∧
      (∀ i, ∀ f : F, ∀ hf : f ∈ (C i).integers, ∃ hf' : s • f ∈ (C i).integers,
        (C i).residue ⟨s • f, hf'⟩ = (C i).residue ⟨f, hf⟩) ∧
      (∀ i, ∀ P ∈ (C i).dom, (C i).placeMap (s • P) = (C i).placeMap P))
    (hSlift : ∀ σ : L ≃+* L, (∀ a : L, a ∈ A ↔ σ a ∈ A) → σ (π : L) = (π : L) →
      (∀ (a : A) (h : σ (a : L) ∈ A), IsLocalRing.residue A ⟨σ (a : L), h⟩ = IsLocalRing.residue A a) →
      ∃ s ∈ S, SemilinearAut.baseAut s = σ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : IsLocalRing.ResidueField A))
    (hSℓ : ∃ s ∈ S, ∃ r : L, r ^ ℓ = (π : L) ∧ SemilinearAut.baseAut s r ≠ r)
    [FiniteDimensional ℚ_[ℓ] (ModularCurve.RationalTateModule ℓ (Pic0 L F))]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    :
    ∀ (v : ↥(⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1)))
      (x : TateModule ℓ (Pic0 L F)), (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x →
      ∀ k : ℕ, ∃ (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)) (Di : Fin n → Divisor L F),
        Pic0.mk ⟨D, hD⟩ = TateModule.proj ℓ (Pic0 L F) k x ∧
        D = ∑ i, Di i ∧ (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) ∧ ∀ i, Divisor.degree (Di i) = 0 := by sorry
