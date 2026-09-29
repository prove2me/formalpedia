-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_mk_eq_forall_mem_support_pow_evalAt_param_eq_of_zsmul_eq_zero_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
-- name    : AlgebraicCurve.exists_mk_eq_forall_mem_support_pow_evalAt_param_eq_of_zsmul_eq_zero_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/f5e1473c-edee-5d2e-98c6-5002ba6df87d
-- title:
--   Kummer-normalised representatives of ℓ^k-torsion classes on a semistable covering
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A \subseteq L$ a valuation subring, and $\pi$ a nonzero element of the maximal ideal of $A$, with $A$ of rank one in the sense that for every $x \in L^\times$ and every $y$ in the maximal ideal some power $y^n$ has valuation at most that of $x$. Let $F$ be a field over $L$ which is a curve over $L$ and essentially of finite type, let $\ell$ be a prime and $k \in \mathbb{N}$. The covering data consist of: fields $\bar F_i$ ($i \in \mathrm{Fin}\,n$) over the residue field of $A$, each a curve and essentially of finite type and with all places rational; component charts $C_i$ (a valuation subring of $F$ with surjective residue map onto $\bar F_i$ with kernel the maximal ideal, a set of places of $F/L$ all of which are rational, a finite node set in the places of $\bar F_i$, and a reduction map on places); annuli $\mathrm{An}_e, \mathrm{An}'_e$ ($e \in \mathrm{Fin}\,m$) with edge maps $\mathrm{src}, \mathrm{tgt}$, node labels $x_s(e), x_t(e)$ and weights $w(e)$, where each pair has equal domain and equal nonzero modulus and the two parameters multiply to the modulus (`hpair`), each modulus is a unit times $\pi^{w(e)}$ (`hw`), and $\mathrm{An}_e$, $\mathrm{An}'_e$ are attached to $C_{\mathrm{src}(e)}$ at $x_s(e)$ and to $C_{\mathrm{tgt}(e)}$ at $x_t(e)$ (`hatt`); the condition that every node of every chart is an end of exactly one edge (`hnodes`); the condition that every place of $F/L$ lies either in exactly one chart domain and no annulus domain, or in exactly one annulus domain and no chart domain (`hcover`); a disc-fibre condition providing, for each non-node place $Q$ of $\bar F_i$, a chart function $T$ with nonzero residue of $Q$-order $1$ whose values at the places above $Q$ lie in the maximal ideal of $A$ and parametrise those places bijectively (`hdisc`); and the genus relation $g(F/L) + n = \sum_i g(\bar F_i) + m + 1$. Given in addition a semistable model $M$ for these data and a descent datum for $M$, the conclusion is: for every class $c$ in $\mathrm{Pic}^0(F/L)$ with $\ell^k c = 0$ there is a degree-zero divisor representing $c$ each of whose support places $P$ either lies in some chart domain $\mathrm{dom}(C_i)$, or lies in some annulus domain $\mathrm{dom}(\mathrm{An}_e)$ and satisfies $(P.\mathrm{evalAt}\,z_e)^{\ell^k} = u\,\pi^{j}$ for some unit $u \in A^\times$ and some $j \in \mathbb{N}$, where $z_e$ is the parameter of $\mathrm{An}_e$.
--
--   This is the normalisation step in the rigid-analytic description of the $\ell$-power torsion of $\mathrm{Pic}^0$ of a curve with semistable reduction over a rank-one valuation ring: torsion classes admit representatives whose annulus-supported part sits at radii whose $\ell^k$-th powers are integral powers of the uniformiser up to units. It is used by the statements describing invariants of the rational Tate module, the chart-supported representation of torsion classes, and the comparison of the Galois action on such representatives.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_mk_eq_forall_mem_support_pow_evalAt_param_eq_of_zsmul_eq_zero_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel.lean

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
    AlgebraicCurve.exists_mk_eq_forall_mem_support_pow_evalAt_param_eq_of_zsmul_eq_zero_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
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
    (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ)
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    :
    ∀ c : Pic0 L F, ((ℓ ^ k : ℕ) : ℤ) • c = 0 →
      ∃ (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)),
        Pic0.mk ⟨D, hD⟩ = c ∧
        ∀ P ∈ D.support, (∃ i, P ∈ (C i).dom) ∨
          ∃ e, P ∈ (An e).dom ∧ ∃ (v : Aˣ) (j : ℕ),
            (P.evalAt (An e).param) ^ (ℓ ^ k) = ((v : A) : L) * (π : L) ^ j := by sorry
