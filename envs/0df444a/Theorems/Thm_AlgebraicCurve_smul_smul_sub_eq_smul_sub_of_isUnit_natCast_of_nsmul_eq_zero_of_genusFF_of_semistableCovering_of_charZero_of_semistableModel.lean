-- Prove2me | Theorems.Thm_AlgebraicCurve_smul_smul_sub_eq_smul_sub_of_isUnit_natCast_of_nsmul_eq_zero_of_genusFF_of_semistableCovering_of_charZero_of_semistableModel
-- name    : AlgebraicCurve.smul_smul_sub_eq_smul_sub_of_isUnit_natCast_of_nsmul_eq_zero_of_genusFF_of_semistableCovering_of_charZero_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/ff6ba880-fed9-5b1a-94f1-1b725731477b
-- title:
--   Level-two unipotence of inertia on prime-to-p torsion of Pic⁰
-- statement:
--   Let $L$ be an algebraically closed field of characteristic $0$, $A \subseteq L$ a valuation subring, $\pi \in A$ a nonzero element of the maximal ideal, and assume that for every nonzero $x \in L$ and every $y$ in the maximal ideal some power $y^n$ has valuation at most that of $x$. Let $F$ be a field over $L$, and let $n, m : \mathbb{N}$, fields $\bar F_i$ over the residue field $\kappa =$ `ResidueField A` for $i \in \mathrm{Fin}\,n$ all of whose places over $\kappa$ are rational, component charts $C_i$ whose domains consist of rational places, annuli $\mathrm{An}_e, \mathrm{An}'_e$ indexed by $e \in \mathrm{Fin}\,m$ with source and target indices $\mathrm{src}, \mathrm{tgt}$, node places $x_s(e), x_t(e)$ on the corresponding $\bar F_i$, and weights $w_e$ be given, subject to: each pair $\mathrm{An}'_e, \mathrm{An}_e$ has the same domain and modulus, the modulus is nonzero in $L$ and equals the product of the two parameters; each modulus is a unit times $\pi^{w_e}$; $\mathrm{An}_e$ is attached to $C_{\mathrm{src}(e)}$ at $x_s(e)$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}(e)}$ at $x_t(e)$; every node of every chart is an end of exactly one annulus, the ends being indexed injectively by $\mathrm{Fin}\,m \oplus \mathrm{Fin}\,m$; every place of $F/L$ lies either in exactly one chart domain and no annulus domain, or in exactly one annulus domain and no chart domain; a disc-fibre clause providing, for each non-node place $Q$ of $\bar F_i$, an element $T$ of the chart's valuation ring with nonzero residue of $Q$-order $1$, lying in the valuation ring of every place of the chart domain above $Q$ with value in the maximal ideal of $A$, and such that each $c$ in the maximal ideal is the value at $T$ of a unique place of the chart domain above $Q$; and the genus identity $\mathrm{genusFF}(L,F) + n = \sum_i \mathrm{genusFF}(\kappa, \bar F_i) + m + 1$, where $\mathrm{genusFF}$ is the $\dim$ of $H^1$ of the zero divisor. Assume further that $F/L$ and each $\bar F_i/\kappa$ are curves in the sense of `IsCurveOver` and essentially of finite type, and fix a semistable model $M$ of this data over $A$ together with a descent datum $D$ for $M$. Let $S$ be a set of semilinear automorphisms of $F$ (pairs of ring automorphisms of $F$ and of $L$ compatible with the structure map) such that each $s \in S$ satisfies the following inertia conditions: its base automorphism preserves membership in $A$, fixes $\pi$, induces the identity on $\kappa$, and multiplies every nonzero element of $L$ by a unit of $A$; and $s$ preserves every chart domain and every annulus domain under the action on places, fixes every $\mathrm{An}_e$ and $\mathrm{An}'_e$ parameter, preserves each chart's valuation ring with unchanged residue, and satisfies $(C_i).\mathrm{placeMap}(s \cdot P) = (C_i).\mathrm{placeMap}(P)$ on each chart domain. Then for all $g, \tau \in S$, every class $x$ in $\mathrm{Pic}^0$ of $F/L$ (degree-zero divisors modulo principal divisors) and every $k : \mathbb{N}$ whose image in $\kappa$ is a unit, $k \cdot x = 0$ implies $\tau \cdot (g \cdot x - x) = g \cdot x - x$.
--
--   This is the level-two unipotence of the inertia action on the prime-to-residue-characteristic torsion of the Jacobian of a semistably covered curve: $(\sigma - 1)^2$ annihilates such torsion, in the chart-and-annulus formulation of semistable reduction, with the arithmetic input of a semistable model and a descent datum. It is proved from the principality criterion [`AlgebraicCurve.mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent`](thm.html#AlgebraicCurve.mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent), and is used in turn for the corresponding statements about iterated differences and about the induced Galois representation on rational torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_smul_smul_sub_eq_smul_sub_of_isUnit_natCast_of_nsmul_eq_zero_of_genusFF_of_semistableCovering_of_charZero_of_semistableModel.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem
    AlgebraicCurve.smul_smul_sub_eq_smul_sub_of_isUnit_natCast_of_nsmul_eq_zero_of_genusFF_of_semistableCovering_of_charZero_of_semistableModel
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type*) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)]
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
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    (S : Set (SemilinearAut L F))
    (hS : ∀ s ∈ S, (∀ a : L, a ∈ A ↔ SemilinearAut.baseAut s a ∈ A) ∧ SemilinearAut.baseAut s (π : L) = (π : L) ∧
      (∀ (a : A) (h : SemilinearAut.baseAut s (a : L) ∈ A),
        IsLocalRing.residue A ⟨SemilinearAut.baseAut s (a : L), h⟩ = IsLocalRing.residue A a) ∧
      (∀ i, ∀ P ∈ (C i).dom, s • P ∈ (C i).dom) ∧ (∀ e, ∀ P ∈ (An e).dom, s • P ∈ (An e).dom) ∧
      (∀ e, s • (An e).param = (An e).param) ∧ (∀ e, s • (An' e).param = (An' e).param) ∧
      (∀ i, ∀ f : F, ∀ hf : f ∈ (C i).integers, ∃ hf' : s • f ∈ (C i).integers,
        (C i).residue ⟨s • f, hf'⟩ = (C i).residue ⟨f, hf⟩) ∧
      (∀ i, ∀ P ∈ (C i).dom, (C i).placeMap (s • P) = (C i).placeMap P) ∧
      (∀ a : L, a ≠ 0 → ∃ u : Aˣ, SemilinearAut.baseAut s a = u * a))
    :
    (∀ g ∈ S, ∀ τ ∈ S, ∀ (x : Pic0 L F) (k : ℕ), IsUnit ((k : ℕ) : IsLocalRing.ResidueField A) →
      k • x = 0 → τ • (g • x - x) = g • x - x) := by sorry
