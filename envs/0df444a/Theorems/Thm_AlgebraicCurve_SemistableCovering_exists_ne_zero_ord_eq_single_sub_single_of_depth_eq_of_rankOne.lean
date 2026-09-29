-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableCovering_exists_ne_zero_ord_eq_single_sub_single_of_depth_eq_of_rankOne
-- name    : AlgebraicCurve.SemistableCovering.exists_ne_zero_ord_eq_single_sub_single_of_depth_eq_of_rankOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/2b71559e-71e8-55ed-9fb2-27368f66cc57
-- title:
--   Equal-depth annulus points differ by chart-supported degree-zero divisors
-- statement:
--   Let $L$ be an algebraically closed field, $A\subseteq L$ a valuation subring with maximal ideal $\mathfrak m_A$ and residue field $\kappa=\mathrm{ResidueField}(A)$, and $\pi\in\mathfrak m_A$ nonzero; assume $A$ has rank one in the sense that for every $x\in L^{\times}$ and every $y\in\mathfrak m_A$ some power $y^{N}$ has valuation at most that of $x$. Let $F$ be a field extension of $L$ which is a curve over $L$ (principal divisors exist, all residue fields of places are finite over $L$, and $\Omega_{F/L}$ is free of rank one) and essentially of finite type over $L$, and let $\bar F_1,\dots,\bar F_n$ be curves over $\kappa$, essentially of finite type, all of whose places are rational. The data are: component charts $C_i$ (each a valuation subring of $F$ with surjective residue map onto $\bar F_i$, a domain of places of $F$, a finite set of nodes among the places of $\bar F_i$, and a reduction map on places, subject to the `ComponentChart` axioms), all places of $(C_i).\mathrm{dom}$ being rational; annuli $\mathrm{An}_e,\mathrm{An}'_e$ ($e\in\{1,\dots,m\}$) with parameters and moduli $\mu_e\in\mathfrak m_A$ satisfying the `Annulus` axioms; edge maps $\mathrm{src},\mathrm{tgt}$ into $\{1,\dots,n\}$; node places $x_s(e)$ of $\bar F_{\mathrm{src}(e)}$ and $x_t(e)$ of $\bar F_{\mathrm{tgt}(e)}$; and weights $w_e\in\mathbb N$. The hypotheses are: $\mathrm{An}'_e$ has the same domain and the same modulus as $\mathrm{An}_e$, $\mu_e\neq0$ in $L$, and the product of the two parameters is the image of $\mu_e$; $\mu_e=u\pi^{w_e}$ for some unit $u$ of $A$; $\mathrm{An}_e$ is attached to $C_{\mathrm{src}(e)}$ at $x_s(e)$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}(e)}$ at $x_t(e)$ in the sense of `IsAttached`; every node of every chart is an end $\langle \mathrm{src}(e),x_s(e)\rangle$ or $\langle \mathrm{tgt}(e),x_t(e)\rangle$ of some annulus, and such an end representing a given node is unique as an element of $\mathrm{Fin}\,m\oplus\mathrm{Fin}\,m$; every place of $F$ over $L$ lies either in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain; for each $i$ and each non-node place $Q$ of $\bar F_i$ there is $T$ in $(C_i).\mathrm{integers}$ with nonzero residue, $\mathrm{ord}_Q$ of that residue equal to $1$, such that every place $P$ of the chart domain reducing to $Q$ has $T$ in its valuation subring with $P.\mathrm{evalAt}\,T\in\mathfrak m_A$, and every $c\in\mathfrak m_A$ is $P.\mathrm{evalAt}\,T$ for exactly one such $P$; and the genus identity $g(F)+n=\sum_i g(\bar F_i)+m+1$, with $g$ the dimension of $H^1(0)$. Finally, fix an edge $e_0$, two distinct places $P\neq P'$ in the domain of $\mathrm{An}_{e_0}$ whose values $P.\mathrm{evalAt}$ and $P'.\mathrm{evalAt}$ on the parameter of $\mathrm{An}_{e_0}$ lie in $A$ and equal $u\pi^{d}$ and $u'\pi^{d}$ for units $u,u'$ of $A$ and the same $d\in\mathbb N$. The conclusion asserts the existence of $f\in F^{\times}$ and a divisor $D_f$ with $D_f(Q)=\mathrm{ord}_Q(f)$ for every place $Q$, such that on every annulus domain $D_f$ agrees with the divisor $[P]-[P']$, and such that $D_f-([P]-[P'])=\sum_{i}D_i$ for divisors $D_i$ with support contained in $(C_i).\mathrm{dom}$ and $\deg D_i=0$ for each $i$.
--
--   This is the two-point case of the lifting of principal divisors from the resolved dual graph of a semistable reduction to principal divisors of $F$: for two points of a single annulus at the same depth the class $[P]-[P']$ has trivial toric coordinates, and the lift can be chosen so that the error is supported on the components and has degree zero on each. It feeds [`AlgebraicCurve.SemistableCovering.exists_ne_zero_ord_eq_single_sub_single_mapDomain_placeMap_mem_principal_of_valuation_eq_of_rankOne`](thm.html#AlgebraicCurve.SemistableCovering.exists_ne_zero_ord_eq_single_sub_single_mapDomain_placeMap_mem_principal_of_valuation_eq_of_rankOne) and [`AlgebraicCurve.exists_ne_zero_ord_eq_of_depthMass_eq_zero_of_semistableCovering_of_rankOne`](thm.html#AlgebraicCurve.exists_ne_zero_ord_eq_of_depthMass_eq_zero_of_semistableCovering_of_rankOne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableCovering_exists_ne_zero_ord_eq_single_sub_single_of_depth_eq_of_rankOne.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.SemistableCovering.exists_ne_zero_ord_eq_single_sub_single_of_depth_eq_of_rankOne
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
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
    (e₀ : Fin m) (P P' : Place L F) (hP : P ∈ (An e₀).dom) (hP' : P' ∈ (An e₀).dom) (hPP' : P ≠ P')
    (d : ℕ) (u u' : Aˣ) (h : P.evalAt (An e₀).param ∈ A) (h' : P'.evalAt (An e₀).param ∈ A)
    (hd : (⟨P.evalAt (An e₀).param, h⟩ : A) = u * π ^ d) (hd' : (⟨P'.evalAt (An e₀).param, h'⟩ : A) = u' * π ^ d)
    :
    ∃ (f : F) (Df : Divisor L F), f ≠ 0 ∧ (∀ Q, Df Q = Q.ord f) ∧
      (∀ e, ∀ Q ∈ (An e).dom, Df Q = (Finsupp.single P 1 - Finsupp.single P' 1 : Divisor L F) Q) ∧
      ∃ Di : Fin n → Divisor L F, Df - (Finsupp.single P 1 - Finsupp.single P' 1) = ∑ i, Di i ∧
        (∀ i, ∀ Q ∈ (Di i).support, Q ∈ (C i).dom) ∧ ∀ i, Divisor.degree (Di i) = 0 := by sorry
