-- Prove2me | Theorems.Thm_AlgebraicCurve_le_add_one_and_exists_finset_card_le_pow_of_chartSupported_principal_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
-- name    : AlgebraicCurve.le_add_one_and_exists_finset_card_le_pow_of_chartSupported_principal_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/b9b6d3c6-130d-517e-8e87-0a126b9fc75b
-- title:
--   Semistable covering: n≤ m+1 and toric k-torsion bound
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A\subseteq L$ a valuation subring with residue field $\kappa$, and $\pi\in\mathfrak m_A$ nonzero; assume $A$ has rank one in the sense that for every $x\in L^{\times}$ and every $y\in\mathfrak m_A$ there is $n$ with $v(y^{n})\le v(x)$. Let $F/L$ be a field extension which is a curve over $L$ (principal divisors exist, residue fields of places are finite over $L$, and $\Omega_{F/L}$ is free of rank one over $F$) and essentially of finite type, and let $\bar F_1,\dots,\bar F_n$ be curves over $\kappa$, essentially of finite type, all of whose places are rational. Given component charts $C_i$ of $F$ along $A$ with residue field $\bar F_i$ (a valuation subring of $F$ with residue map onto $\bar F_i$, a set of places of $F$ as domain, a finite set of nodes in $\bar F_i$ and a place map), all places in $C_i$'s domain being rational; annuli $An_e,An'_e$ ($e<m$) with $\mathrm{src}(e),\mathrm{tgt}(e)<n$ and nodes $xs_e$ of $\bar F_{\mathrm{src}(e)}$, $xt_e$ of $\bar F_{\mathrm{tgt}(e)}$, and weights $w_e$, such that $An'_e$ has the same domain and the same (nonzero) modulus as $An_e$ with the product of the two parameters equal to the image of that modulus, each modulus being a unit times $\pi^{w_e}$, and $An_e$ attached to $C_{\mathrm{src}(e)}$ at $xs_e$ and $An'_e$ to $C_{\mathrm{tgt}(e)}$ at $xt_e$; the hypothesis that each node of each chart is hit by exactly one of the $2m$ annulus ends; the hypothesis that every place of $F$ lies either in exactly one chart domain and no annulus domain, or in exactly one annulus domain and no chart domain; the disc-fibre hypothesis that for each $i$ and each non-node place $Q$ of $\bar F_i$ there is $T$ in the integers of $C_i$ whose residue is nonzero with $\mathrm{ord}_Q$ equal to $1$, such that $T$ lies in every place of $C_i$'s domain above $Q$ with value in $\mathfrak m_A$ there, and such that for every $c\in\mathfrak m_A$ there is a unique place $P$ of $C_i$'s domain above $Q$ with $P(T)=c$; and the genus identity $g(F/L)+n=\sum_i g(\bar F_i/\kappa)+m+1$, where the genus is the $\kappa$- respectively $L$-dimension of $H^1$ of the zero divisor. Assume finally given a semistable model $M$ over $A$ for these data together with a descent datum for $M$. Then $n\le m+1$, and for every natural number $k$ whose image in $\kappa$ is a unit there is a finite set $B$ of classes in $\mathrm{Pic}^0(F/L)$ (degree-zero divisors modulo principal ones) with $|B|\le k^{m+1-n}$ containing every class $c$ with $kc=0$ that is toric for the covering, that is, every $c$ represented by a degree-zero divisor $\sum_{i} D_i$ in which each $D_i$ is supported in the domain of $C_i$, has degree zero, and pushes forward under the place map of $C_i$ to a principal divisor of $\bar F_i/\kappa$.
--
--   This is the bound on the toric part of the $k$-torsion of the Jacobian of a semistably covered curve, in the style of the specialisation of the Picard functor and of component groups of Néron models, here in the form needed when the covering comes from a semistable model with a descent datum over a Noetherian Henselian base. It is used in the estimate [`AlgebraicCurve.finrank_ker_reduction_add_le_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel`](thm.html#AlgebraicCurve.finrank_ker_reduction_add_le_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel) for the kernel of reduction on torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_le_add_one_and_exists_finset_card_le_pow_of_chartSupported_principal_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem
    AlgebraicCurve.le_add_one_and_exists_finset_card_le_pow_of_chartSupported_principal_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
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
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    :
    n ≤ m + 1 ∧
    ∀ k : ℕ, IsUnit ((k : ℕ) : IsLocalRing.ResidueField A) →
      ∃ B : Finset (Pic0 L F), B.card ≤ k ^ (m + 1 - n) ∧
        ∀ c : Pic0 L F, (k : ℤ) • c = 0 →
          (∃ (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)) (Di : Fin n → Divisor L F),
            Pic0.mk ⟨D, hD⟩ = c ∧ D = ∑ i, Di i ∧ (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) ∧
            (∀ i, Divisor.degree (Di i) = 0) ∧
            ∀ i, Finsupp.mapDomain (C i).placeMap (Di i) ∈
              Divisor.principal (K := IsLocalRing.ResidueField A) (F := Fbar i)) →
          c ∈ B := by sorry
