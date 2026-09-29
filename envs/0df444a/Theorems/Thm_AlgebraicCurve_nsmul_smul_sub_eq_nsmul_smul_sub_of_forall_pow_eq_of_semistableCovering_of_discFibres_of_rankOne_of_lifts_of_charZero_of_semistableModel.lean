-- Prove2me | Theorems.Thm_AlgebraicCurve_nsmul_smul_sub_eq_nsmul_smul_sub_of_forall_pow_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- name    : AlgebraicCurve.nsmul_smul_sub_eq_nsmul_smul_sub_of_forall_pow_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/256b5d5f-01b8-5917-8014-ab9c084570ce
-- title:
--   Monodromy on ℓ^k-torsion of Pic⁰ factors through roots of π
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A \subseteq L$ a valuation subring, and $\pi \in A$ a nonzero element of the maximal ideal, with $A$ of rank one in the sense that for every $x \neq 0$ in $L$ and every $y$ in the maximal ideal some power $y^n$ has valuation at most that of $x$. Let $F/L$ be a field extension which is a curve over $L$ and essentially of finite type, and let there be given the data of a semistable covering: fields $\bar F_i$ ($i \in \mathrm{Fin}\,n$) over the residue field of $A$, all of whose places are rational and each of which is a curve, essentially of finite type; component charts $C_i$ (valuation subrings of $F$ with surjective residue map onto $\bar F_i$ whose kernel is the maximal ideal, a domain of places of $F/L$, a finite set of nodes, and a map to places of $\bar F_i$) all of whose places in the domain are rational; annuli $An_e$, $An'_e$ ($e \in \mathrm{Fin}\,m$) with source and target indices $\mathrm{src}, \mathrm{tgt}$, node places $x_s(e), x_t(e)$, and weights $w_e$; hypotheses that $An'_e$ and $An_e$ have the same domain and the same (nonzero) modulus, their parameters multiplying to the image of that modulus, that each modulus is a unit times $\pi^{w_e}$, that $An_e$ is attached to $C_{\mathrm{src}(e)}$ at $x_s(e)$ and $An'_e$ to $C_{\mathrm{tgt}(e)}$ at $x_t(e)$, that every node of every chart is an endpoint of exactly one edge-end, that every place of $F/L$ lies either in exactly one chart domain and no annulus domain or in exactly one annulus domain and no chart domain, a discs-fibre condition producing for each non-node place $Q$ of $\bar F_i$ a function $T$ in the integers of $C_i$ with nonzero residue of order $1$ at $Q$, lying in the valuation ring of each place above $Q$ with value in the maximal ideal of $A$ and realising each such value at a unique place above $Q$, and the genus relation $g(F/L) + n = \sum_i g(\bar F_i) + m + 1$. Let $S$ be a set of semilinear automorphisms of $F$ (pairs consisting of a ring automorphism of $F$ and one of $L$ compatible with the structure map) each of which preserves $A$, fixes $\pi$, acts trivially on the residue field of $A$, preserves each chart domain and each annulus domain, fixes every parameter of $An_e$ and of $An'_e$, preserves the integers of each chart with unchanged residues, and commutes with each $\mathrm{placeMap}$; assume every ring automorphism of $L$ preserving $A$, fixing $\pi$ and trivial on residues is the base automorphism of some member of $S$. Let $\ell$ be a prime invertible in the residue field of $A$, assume some $s \in S$ moves some $\ell$-th root of $\pi$, and assume $\mathbb{Q}_\ell \otimes_{\mathbb{Z}_\ell} T_\ell(\mathrm{Pic}^0(F/L))$ is finite-dimensional over $\mathbb{Q}_\ell$. Finally let $M$ be a semistable model of the covering data over $A$ and $D$ a descent datum for $M$. Then for all $s, s' \in S$ and all natural numbers $k, a, b$ such that $(\mathrm{baseAut}\,s)^a$ and $(\mathrm{baseAut}\,s')^b$ agree on every $r \in L$ with $r^{\ell^k} = \pi$, every class $P$ in $\mathrm{Pic}^0(F/L)$ (degree-zero divisors modulo principal ones) killed by $\ell^k$ satisfies $a\,(s \cdot P - P) = b\,(s' \cdot P - P)$.
--
--   This is the Kummer-type congruence for the monodromy action on torsion of the Jacobian of a semistably covered curve: modulo $\ell^k$-torsion, the action of the semilinear automorphism group on $\mathrm{Pic}^0$ depends only on the action on $\ell^k$-th roots of the uniformiser $\pi$. It is the arithmetic form of the statement, with a semistable model and descent datum over $A$ available, and it feeds the construction of the linear map describing the action of $S$ on torsion in [`AlgebraicCurve.exists_linearMap_forall_sub_one_eq_smul_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel`](thm.html#AlgebraicCurve.exists_linearMap_forall_sub_one_eq_smul_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_nsmul_smul_sub_eq_nsmul_smul_sub_of_forall_pow_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.lean

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
    AlgebraicCurve.nsmul_smul_sub_eq_nsmul_smul_sub_of_forall_pow_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
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
    ∀ s ∈ S, ∀ s' ∈ S, ∀ (k a b : ℕ),
      (∀ r : L, r ^ (ℓ ^ k) = (π : L) →
        ((SemilinearAut.baseAut s) ^ a) r = ((SemilinearAut.baseAut s') ^ b) r) →
      ∀ P : Pic0 L F, ((ℓ ^ k : ℕ) : ℤ) • P = 0 → a • (s • P - P) = b • (s' • P - P) := by sorry
