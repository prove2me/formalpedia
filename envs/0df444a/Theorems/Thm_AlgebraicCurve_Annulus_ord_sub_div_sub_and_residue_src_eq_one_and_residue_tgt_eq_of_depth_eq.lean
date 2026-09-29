-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_ord_sub_div_sub_and_residue_src_eq_one_and_residue_tgt_eq_of_depth_eq
-- name    : AlgebraicCurve.Annulus.ord_sub_div_sub_and_residue_src_eq_one_and_residue_tgt_eq_of_depth_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/5f068574-9aa8-51e2-9af7-0b9cc5f7cd53
-- title:
--   Equal-depth ratio on an annulus: divisor and end residues
-- statement:
--   Let $L$ be an algebraically closed field, $A\subseteq L$ a valuation subring, and $\pi\in A$ a nonzero element of the maximal ideal; let $F$ be a field over $L$ which is a curve over $L$ (principal divisors exist, residue fields of places are finite over $L$, and $\Omega_{F/L}$ is free of rank one) and essentially of finite type over $L$. Fix $n,m$, fields $\bar F_i$ ($i\in\mathrm{Fin}\,n$) over the residue field $k$ of $A$ each having principal divisors of degree zero and all of whose places are rational, component charts $C_i$ of $F$ along $A$ with values in $\bar F_i$ whose domains consist of rational places, annuli $\mathrm{An}_e,\mathrm{An}'_e$ ($e\in\mathrm{Fin}\,m$), maps $\mathrm{src},\mathrm{tgt}$ to $\mathrm{Fin}\,n$, places $x_s(e)$ of $\bar F_{\mathrm{src}(e)}$ and $x_t(e)$ of $\bar F_{\mathrm{tgt}(e)}$, and $w:\mathrm{Fin}\,m\to\mathbb N$, subject to: each pair $\mathrm{An}'_e,\mathrm{An}_e$ has the same domain and the same modulus $\mu_e$, with $\mu_e\neq0$ in $L$ and the product of the two parameters equal to the image of $\mu_e$; $\mu_e$ is a unit of $A$ times $\pi^{w(e)}$; $\mathrm{An}_e$ is attached to $C_{\mathrm{src}(e)}$ at $x_s(e)$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}(e)}$ at $x_t(e)$ (the attachment point is a node, the annulus parameter lies in the chart's integers and its residue has order one there, together with the unit-comparison clause of `IsAttached`); every node of every chart is one of these attachment points, and the assignment $\mathrm{Fin}\,m\oplus\mathrm{Fin}\,m\to\coprod_j\mathrm{Place}(k,\bar F_j)$ given by sources and targets takes each node as value at most once; and every place of $F/L$ lies either in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain. Fix $e_0$, write $z$ for the parameter of $\mathrm{An}_{e_0}$, and let $P\neq P'$ be places in $\mathrm{An}_{e_0}.\mathrm{dom}$ whose values $z(P)=P.\mathrm{evalAt}\,z$ and $z(P')$ lie in $A$ and satisfy $z(P)=u\pi^{d}$, $z(P')=u'\pi^{d}$ for some $d\in\mathbb N$ and units $u,u'\in A^\times$. Then, setting $g=(z-z(P))/(z-z(P'))$ in $F$ (values transported along $L\to F$): $g\neq 0$; for every place $Q$ of $F/L$ one has $\mathrm{ord}_Q g=\mathrm{ord}_Q(z-z(P))-\mathrm{ord}_Q(z-z(P'))$; for every $Q$ in $\mathrm{An}_{e_0}.\mathrm{dom}$ one has $\mathrm{ord}_Q g=(\delta_P-\delta_{P'})(Q)$, i.e. the restriction of $g$'s divisor to the annulus is $[P]-[P']$; $g$ lies in the integers of $C_{\mathrm{src}(e_0)}$ with residue $1$; and $g$ lies in the integers of $C_{\mathrm{tgt}(e_0)}$ with residue the image in $\bar F_{\mathrm{tgt}(e_0)}$ of the residue class of $u\,u'^{-1}$ in $k$.
--
--   This is the explicit toric coordinate attached to a pair of places of equal depth on one annulus of a semistable covering: the function $g$ has divisor $[P]-[P']$ on that annulus, reduces to $1$ at the source end and to the residue of $u/u'$ at the target end. It is used in [`AlgebraicCurve.SemistableCovering.ord_eq_single_sub_single_of_forall_residue_evalAt_ne_zero_of_rankOne`](thm.html#AlgebraicCurve.SemistableCovering.ord_eq_single_sub_single_of_forall_residue_evalAt_ne_zero_of_rankOne), where such functions realise prescribed degree-zero divisors supported on a single annulus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_ord_sub_div_sub_and_residue_src_eq_one_and_residue_tgt_eq_of_depth_eq.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Annulus.ord_sub_div_sub_and_residue_src_eq_one_and_residue_tgt_eq_of_depth_eq
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (F : Type*) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, HasPrincipalDivisors (IsLocalRing.ResidueField A) (Fbar i)]
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
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (e₀ : Fin m) (P P' : Place L F) (hP : P ∈ (An e₀).dom) (hP' : P' ∈ (An e₀).dom) (hPP' : P ≠ P')
    (d : ℕ) (u u' : Aˣ) (h : P.evalAt (An e₀).param ∈ A) (h' : P'.evalAt (An e₀).param ∈ A)
    (hd : (⟨P.evalAt (An e₀).param, h⟩ : A) = u * π ^ d)
    (hd' : (⟨P'.evalAt (An e₀).param, h'⟩ : A) = u' * π ^ d)
    :
    let g : F := ((An e₀).param - algebraMap L F (P.evalAt (An e₀).param)) /
      ((An e₀).param - algebraMap L F (P'.evalAt (An e₀).param))
    g ≠ 0 ∧
      (∀ Q : Place L F, Q.ord g = Q.ord ((An e₀).param - algebraMap L F (P.evalAt (An e₀).param)) -
        Q.ord ((An e₀).param - algebraMap L F (P'.evalAt (An e₀).param))) ∧
      (∀ Q ∈ (An e₀).dom, Q.ord g = (Finsupp.single P 1 - Finsupp.single P' 1 : Divisor L F) Q) ∧
      (∃ hs : g ∈ (C (src e₀)).integers, (C (src e₀)).residue ⟨g, hs⟩ = 1) ∧
      (∃ ht : g ∈ (C (tgt e₀)).integers, (C (tgt e₀)).residue ⟨g, ht⟩ =
        algebraMap (IsLocalRing.ResidueField A) (Fbar (tgt e₀)) (IsLocalRing.residue A ((u : A) * ↑u'⁻¹))) := by sorry
