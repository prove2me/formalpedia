-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableCovering_ord_eq_single_sub_single_of_forall_residue_evalAt_ne_zero_of_rankOne
-- name    : AlgebraicCurve.SemistableCovering.ord_eq_single_sub_single_of_forall_residue_evalAt_ne_zero_of_rankOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/17d041cb-3490-5475-827f-49fbd648a4c3
-- title:
--   Divisor of g restricted to the annuli is [P']-[P]
-- statement:
--   Let $L$ be an algebraically closed field and $A\subseteq L$ a valuation subring, with maximal ideal $\mathfrak m_A$ and residue field $\kappa=\mathrm{ResidueField}(A)$, let $\pi\in\mathfrak m_A$ be nonzero, and assume $A$ has rank one in the form: for every nonzero $x\in L$ and every $y\in\mathfrak m_A$ there is $n$ with $v_A(y^n)\le v_A(x)$. Let $F/L$ be a field extension, and fix $n,m$, fields $\bar F_i/\kappa$ ($i\in\mathrm{Fin}\,n$) all of whose places over $\kappa$ are rational, component charts $C_i$ of $F$ over $A$ with values in $\bar F_i$ all of whose domain places are rational, and annuli $\mathrm{An}_e,\mathrm{An}'_e$ ($e\in\mathrm{Fin}\,m$) with source and target indices $\mathrm{src}\,e,\mathrm{tgt}\,e$, node places $x_s(e)$ in $\bar F_{\mathrm{src}\,e}$, $x_t(e)$ in $\bar F_{\mathrm{tgt}\,e}$ and weights $w(e)$. The configuration hypotheses are: $\mathrm{An}'_e$ has the same domain and the same modulus as $\mathrm{An}_e$, that modulus is nonzero in $L$ and the product of the two parameters is its image in $F$; the modulus of $\mathrm{An}_e$ is a unit times $\pi^{w(e)}$; $\mathrm{An}_e$ is attached to $C_{\mathrm{src}\,e}$ at $x_s(e)$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}\,e}$ at $x_t(e)$; every node of every chart is an end of some annulus, and the assignment of the $2m$ ends to pairs (chart, node) is injective at nodes; every place of $F/L$ lies either in exactly one chart domain and no annulus domain, or in exactly one annulus domain and no chart domain; for each $i$ and each non-node place $Q$ of $\bar F_i$ there is $T$ in the integers of $C_i$ whose residue is nonzero with $\mathrm{ord}_Q=1$, which lies in every $P$ of the chart domain above $Q$ with $P$-value in $\mathfrak m_A$, and such that each $c\in\mathfrak m_A$ is the value of $T$ at exactly one such $P$; and the genus identity $g(F/L)+n=\sum_i g(\bar F_i/\kappa)+m+1$. Assume further that $F/L$ and each $\bar F_i/\kappa$ are curves (in the sense of `IsCurveOver`) and essentially of finite type. Fix $e_0$ and two distinct places $P\ne P'$ in the domain of $\mathrm{An}_{e_0}$ whose values on the parameter of $\mathrm{An}_{e_0}$ lie in $A$ and equal $u\pi^d$ and $u'\pi^d$ for units $u,u'\in A^\times$ and the same $d\in\mathbb N$. Finally let $g\in F$ be nonzero with $\mathrm{ord}_Q g\ge 0$ at every place $Q$ of every annulus domain other than $P$ and $P'$, $\mathrm{ord}_P g\ge -1$, $\mathrm{ord}_{P'} g\ge 1$, and such that for every $i$ the element $g$ lies in the integers of $C_i$, has nonzero residue there, and that residue lies in the valuation subring of each node $x$ of $C_i$ with nonzero value at $x$. Then there is a divisor $D_g$ on $F/L$ with $D_g(Q)=\mathrm{ord}_Q g$ at every place $Q$, such that $D_g$ coincides with $[P']-[P]$ at every place of every annulus domain, and such that $D_g-([P']-[P])$ is a sum $\sum_i D_i$ of divisors $D_i$ supported in the domain of $C_i$ and of degree zero.
--
--   This is the cleanliness step in the analysis of principal divisors along a semistable covering: a function which is integral with node-nonvanishing residues on every chart and has prescribed behaviour at two points of one annulus has no further zeros or poles on any annulus, so that the annulus part of its divisor is exactly $[P']-[P]$ and the remainder splits into degree-zero chart divisors. It is used by [`AlgebraicCurve.SemistableCovering.exists_ne_zero_ord_eq_single_sub_single_of_depth_eq_of_rankOne`](thm.html#AlgebraicCurve.SemistableCovering.exists_ne_zero_ord_eq_single_sub_single_of_depth_eq_of_rankOne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableCovering_ord_eq_single_sub_single_of_forall_residue_evalAt_ne_zero_of_rankOne.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.SemistableCovering.ord_eq_single_sub_single_of_forall_residue_evalAt_ne_zero_of_rankOne
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
    (g : F) (hg0 : g ≠ 0)
    (hgann : ∀ e, ∀ Q ∈ (An e).dom, Q ≠ P → Q ≠ P' → 0 ≤ Q.ord g)
    (hgP : -1 ≤ P.ord g) (hgP' : 1 ≤ P'.ord g)
    (hgres : ∀ i, ∃ hg : g ∈ (C i).integers, (C i).residue ⟨g, hg⟩ ≠ 0 ∧ ∀ x ∈ (C i).nodes,
      (C i).residue ⟨g, hg⟩ ∈ x.toValuationSubring ∧ x.evalAt ((C i).residue ⟨g, hg⟩) ≠ 0)
    :
    ∃ Dg : Divisor L F, (∀ Q, Dg Q = Q.ord g) ∧
      (∀ e, ∀ Q ∈ (An e).dom, Dg Q = (Finsupp.single P' 1 - Finsupp.single P 1 : Divisor L F) Q) ∧
      ∃ Di : Fin n → Divisor L F, Dg - (Finsupp.single P' 1 - Finsupp.single P 1) = ∑ i, Di i ∧
        (∀ i, ∀ Q ∈ (Di i).support, Q ∈ (C i).dom) ∧ ∀ i, Divisor.degree (Di i) = 0 := by sorry
