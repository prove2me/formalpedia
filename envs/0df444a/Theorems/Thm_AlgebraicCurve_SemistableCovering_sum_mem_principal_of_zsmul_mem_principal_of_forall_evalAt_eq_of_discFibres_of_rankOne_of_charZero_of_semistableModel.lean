-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableCovering_sum_mem_principal_of_zsmul_mem_principal_of_forall_evalAt_eq_of_discFibres_of_rankOne_of_charZero_of_semistableModel
-- name    : AlgebraicCurve.SemistableCovering.sum_mem_principal_of_zsmul_mem_principal_of_forall_evalAt_eq_of_discFibres_of_rankOne_of_charZero_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/35085dcd-5a95-56c8-a95b-985831751a8b
-- title:
--   Principality of glued chart divisors along a semistable covering
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A\subseteq L$ a valuation subring with residue field $\kappa$, and $\pi$ a nonzero element of the maximal ideal of $A$; assume the rank-one condition that for every $x\in L^{\times}$ and every $y$ in the maximal ideal of $A$ some power $y^{n}$ has valuation at most that of $x$. Let $F$ be a field over $L$, and let $\bar F_{1},\dots,\bar F_{n}$ be fields over $\kappa$ all of whose places over $\kappa$ are rational (the residue map to $\kappa$ being surjective), together with component charts $C_{i}$ of $F$ along $A$ with values in $\bar F_{i}$, all places of $F$ in the chart domains being rational. Let $An_{e},An'_{e}$ ($e\in\{1,\dots,m\}$) be annuli over $A$ in $F$, with edge maps $\mathrm{src},\mathrm{tgt}$ into $\{1,\dots,n\}$ and node places $xs_{e}$ of $\bar F_{\mathrm{src}(e)}$, $xt_{e}$ of $\bar F_{\mathrm{tgt}(e)}$, and weights $w_{e}\in\mathbb{N}$, subject to: $An'_{e}$ and $An_{e}$ have the same domain and the same modulus, that modulus is nonzero in $L$ and the product of the two parameters is the image of the modulus in $F$; each modulus is a unit times $\pi^{w_{e}}$; $An_{e}$ is attached to $C_{\mathrm{src}(e)}$ at $xs_{e}$ and $An'_{e}$ to $C_{\mathrm{tgt}(e)}$ at $xt_{e}$ (the point is a node of the chart, the annulus parameter lies in the chart's ring of integers with residue of order $1$ at the node, and the slope condition of `IsAttached` holds); every node of every chart occurs as an end $\langle\mathrm{src}(e),xs_{e}\rangle$ or $\langle\mathrm{tgt}(e),xt_{e}\rangle$, and the map from $\{1,\dots,m\}\sqcup\{1,\dots,m\}$ given by these ends is injective over each node; every place of $F$ lies either in exactly one chart domain and no annulus domain, or in exactly one annulus domain and no chart domain; for each non-node place $Q$ of $\bar F_{i}$ there is $T$ in the integers of $C_{i}$ whose residue is nonzero of order $1$ at $Q$, such that every place $P$ of the chart domain above $Q$ has $T$ in its valuation ring with $P.\mathrm{evalAt}\,T$ in the maximal ideal of $A$, and such that each $c$ in the maximal ideal of $A$ is the value $P.\mathrm{evalAt}\,T$ for exactly one place $P$ of the domain above $Q$ (the disc-fibre condition); and the genus identity $g(F/L)+n=\sum_{i}g(\bar F_{i}/\kappa)+m+1$ for the genera $\mathrm{genusFF}$. Assume further that $F$ is a curve over $L$ and each $\bar F_{i}$ a curve over $\kappa$, with the respective essential finite type conditions, and fix a semistable model $M$ of this data together with a descent datum $D$ for $M$. Finally let $E_{i}$ be divisors of $F$ over $L$ with $E_{i}$ supported in the domain of $C_{i}$, let $g_{i}\in\bar F_{i}$ be nonzero with $\mathrm{mapDomain}$ of $E_{i}$ along the place map of $C_{i}$ equal to the order divisor of $g_{i}$ at every place, and suppose the values $xs_{e}.\mathrm{evalAt}\,g_{\mathrm{src}(e)}=xt_{e}.\mathrm{evalAt}\,g_{\mathrm{tgt}(e)}$ agree for every edge $e$. Then, for $k\in\mathbb{N}$ whose image in $\kappa$ is a unit, if $k\cdot\sum_{i}E_{i}$ is principal (equal to the order divisor of some nonzero element of $F$), so is $\sum_{i}E_{i}$.
--
--   This is the torsion-killing step in the theory of semistable coverings of a curve along a rank-one valuation ring: a divisor assembled from chart-supported pieces whose chartwise reductions are principal with matching values at the nodes has principal class as soon as a multiple by a residue-characteristic unit is principal. It is the characteristic-zero variant that takes as input a semistable model with descent datum, and it feeds the bound on the number of components and on chart-supported principal classes proved in [`AlgebraicCurve.le_add_one_and_exists_finset_card_le_pow_of_chartSupported_principal_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel`](thm.html#AlgebraicCurve.le_add_one_and_exists_finset_card_le_pow_of_chartSupported_principal_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableCovering_sum_mem_principal_of_zsmul_mem_principal_of_forall_evalAt_eq_of_discFibres_of_rankOne_of_charZero_of_semistableModel.lean

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
    AlgebraicCurve.SemistableCovering.sum_mem_principal_of_zsmul_mem_principal_of_forall_evalAt_eq_of_discFibres_of_rankOne_of_charZero_of_semistableModel
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
    (E : Fin n → Divisor L F) (hE : ∀ i, ∀ P ∈ (E i).support, P ∈ (C i).dom)
    (g : ∀ i, Fbar i) (hg0 : ∀ i, g i ≠ 0)
    (hg : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i),
      Finsupp.mapDomain (C i).placeMap (E i) Q = Q.ord (g i))
    (hglue : ∀ e, (xs e).evalAt (g (src e)) = (xt e).evalAt (g (tgt e)))
    (k : ℕ) (hk : IsUnit ((k : ℕ) : IsLocalRing.ResidueField A))
    (hkE : (k : ℤ) • (∑ i, E i) ∈ Divisor.principal (K := L) (F := F)) :
    (∑ i, E i) ∈ Divisor.principal (K := L) (F := F) := by sorry
