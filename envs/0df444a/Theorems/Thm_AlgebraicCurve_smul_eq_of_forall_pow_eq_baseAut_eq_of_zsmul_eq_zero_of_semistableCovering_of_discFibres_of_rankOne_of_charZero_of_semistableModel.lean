-- Prove2me | Theorems.Thm_AlgebraicCurve_smul_eq_of_forall_pow_eq_baseAut_eq_of_zsmul_eq_zero_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
-- name    : AlgebraicCurve.smul_eq_of_forall_pow_eq_baseAut_eq_of_zsmul_eq_zero_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/47b59d5d-bd42-529a-b4d5-a6c2466b5654
-- title:
--   Automorphisms fixing ℓ^k-th roots of π fix ℓ^k-torsion
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A \subseteq L$ a valuation subring, and $\pi \in A$ a nonzero element of the maximal ideal, with $A$ of rank one in the sense that for every $x \in L^{\times}$ and every $y$ in the maximal ideal some power $y^n$ has valuation at most that of $x$. Let $F$ be a field over $L$ which is a curve over $L$ (in the sense of the class `IsCurveOver`: principal divisors, finite residue extensions, and $\Omega_{F/L}$ free of rank one) and essentially of finite type over $L$, and let $\bar F_1,\dots,\bar F_n$ be fields over the residue field $\kappa$ of $A$, each a curve over $\kappa$ and essentially of finite type, all of whose places are rational. The covering data consist of component charts $C_i$ of $F$ along $A$ with reduction to $\bar F_i$, all places in $(C_i).\mathrm{dom}$ being rational; annuli $An_e, An'_e$ for $e \in \{1,\dots,m\}$ with source and target indices $src(e), tgt(e)$, nodes $xs_e \in \bar F_{src(e)}$, $xt_e \in \bar F_{tgt(e)}$, and weights $w_e \in \mathbb{N}$; and the hypotheses that $An'_e$ and $An_e$ have the same domain and the same (nonzero) modulus with the product of their parameters equal to the image of that modulus, that the modulus is a unit times $\pi^{w_e}$, that $An_e$ is attached to $C_{src(e)}$ at $xs_e$ and $An'_e$ to $C_{tgt(e)}$ at $xt_e$, that every node of every chart is an endpoint of an annulus and that the $2m$ endpoint labels hit each node at most once, that every place of $F$ lies either in exactly one chart domain and no annulus domain or in exactly one annulus domain and no chart domain, that each non-node place $Q$ of $\bar F_i$ admits a disc parameter, namely $T$ in the chart integers whose residue is nonzero with $\mathrm{ord}_Q = 1$, lying in the valuation ring of each place of the chart domain above $Q$ with value in the maximal ideal, and realising each element of the maximal ideal as the value at exactly one such place, and finally the genus identity $\mathrm{genusFF}(F/L) + n = \sum_i \mathrm{genusFF}(\bar F_i/\kappa) + m + 1$. Let $g$ be a semilinear automorphism of $F$, i.e. a ring automorphism of $F$ together with an automorphism $\sigma = \mathrm{baseAut}(g)$ of $L$ compatible with $L \to F$, such that $\sigma$ stabilises $A$ ($a \in A$ iff $\sigma a \in A$), fixes $\pi$ and induces the identity on $\kappa$, while $g$ maps each chart domain and each annulus domain into itself, fixes every parameter of every $An_e$ and $An'_e$, preserves the integers of each chart and commutes with its residue map, and commutes with each $placeMap$. Let $\ell$ be a prime which is a unit in $\kappa$, let $k \in \mathbb{N}$, and assume $\sigma$ fixes every $r \in L$ with $r^{\ell^k} = \pi$. Finally let $M$ be a semistable model of this covering data over $A$ and $D$ a descent datum for $M$. Then for every class $c \in \mathrm{Pic}^0(F/L)$ with $\ell^k c = 0$ one has $g \cdot c = c$.
--
--   This is the statement that a semilinear automorphism of inertia type, whose constant part fixes the $\ell^k$-th roots of the uniformiser, acts trivially on the $\ell^k$-torsion of the degree-zero divisor class group of a curve admitting a semistable covering; it is the arithmetic form of the result, with a semistable model and its descent datum among the hypotheses. It feeds into the comparison of $n$-fold multiples of differences of Galois translates used in the analysis of the Galois action on torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_smul_eq_of_forall_pow_eq_baseAut_eq_of_zsmul_eq_zero_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem
    AlgebraicCurve.smul_eq_of_forall_pow_eq_baseAut_eq_of_zsmul_eq_zero_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
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
    (g : SemilinearAut L F)
    (hg : (∀ a : L, a ∈ A ↔ SemilinearAut.baseAut g a ∈ A) ∧ SemilinearAut.baseAut g (π : L) = (π : L) ∧
      (∀ (a : A) (h : SemilinearAut.baseAut g (a : L) ∈ A),
        IsLocalRing.residue A ⟨SemilinearAut.baseAut g (a : L), h⟩ = IsLocalRing.residue A a) ∧
      (∀ i, ∀ P ∈ (C i).dom, g • P ∈ (C i).dom) ∧ (∀ e, ∀ P ∈ (An e).dom, g • P ∈ (An e).dom) ∧
      (∀ e, g • (An e).param = (An e).param) ∧ (∀ e, g • (An' e).param = (An' e).param) ∧
      (∀ i, ∀ f : F, ∀ hf : f ∈ (C i).integers, ∃ hf' : g • f ∈ (C i).integers,
        (C i).residue ⟨g • f, hf'⟩ = (C i).residue ⟨f, hf⟩) ∧
      (∀ i, ∀ P ∈ (C i).dom, (C i).placeMap (g • P) = (C i).placeMap P))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : IsLocalRing.ResidueField A))
    (k : ℕ) (hfix : ∀ r : L, r ^ (ℓ ^ k) = (π : L) → SemilinearAut.baseAut g r = r)
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    :
    ∀ c : Pic0 L F, ((ℓ ^ k : ℕ) : ℤ) • c = 0 → g • c = c := by sorry
