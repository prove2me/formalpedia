-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_ne_zero_ord_eq_of_depthMass_eq_zero_of_semistableCovering_of_rankOne
-- name    : AlgebraicCurve.exists_ne_zero_ord_eq_of_depthMass_eq_zero_of_semistableCovering_of_rankOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/04553d51-cc1b-52c6-8f48-626a422024e3
-- title:
--   Exact annulus lifting for depth-balanced divisors, rank-one base
-- statement:
--   Let $L$ be an algebraically closed field and $A\subseteq L$ a valuation subring, with $\pi\in A$ a nonzero element of its maximal ideal, and assume $A$ has rank one in the sense that for every $x\in L^{\times}$ and every $y$ in the maximal ideal some power satisfies $v(y^{n})\le v(x)$. Let $F$ be a field over $L$, let $n,m$ be natural numbers and let $\bar F_0,\dots,\bar F_{n-1}$ be fields over the residue field $\kappa$ of $A$, all of whose places (valuation subrings containing $\kappa$, proper, with principal ideals) are rational, i.e. $\kappa$ surjects onto their residue fields. Given component charts $C_i$ over $A$ with values in $\bar F_i$ all of whose places in $(C_i).\mathrm{dom}$ are rational; annuli $\mathrm{An}_e,\mathrm{An}'_e$ in $F$ over $A$ with edge maps $\mathrm{src},\mathrm{tgt}:\mathrm{Fin}\,m\to\mathrm{Fin}\,n$, node places $x^{s}_e$ of $\bar F_{\mathrm{src}(e)}$, $x^{t}_e$ of $\bar F_{\mathrm{tgt}(e)}$ and weights $w_e\in\mathbb N$; assume for each $e$ that $\mathrm{An}'_e$ has the same domain and modulus as $\mathrm{An}_e$, that this modulus $\mu_e$ is nonzero in $L$, that the two parameters multiply to $\mu_e$, that $\mu_e=u\pi^{w_e}$ for some unit $u$ of $A$, and that $\mathrm{An}_e$ is attached to $C_{\mathrm{src}(e)}$ at $x^{s}_e$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}(e)}$ at $x^{t}_e$; assume every node $x$ of every $C_i$ is of the form $\langle\mathrm{src}(e),x^{s}_e\rangle$ or $\langle\mathrm{tgt}(e),x^{t}_e\rangle$ and that this annulus end is unique (as an element of $\mathrm{Fin}\,m\oplus\mathrm{Fin}\,m$); assume every place of $F$ over $L$ lies either in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain; assume the disc-fibre property: for every non-node place $Q$ of $\bar F_i$ there is $T$ in the chart's integers whose residue is nonzero with $Q.\mathrm{ord}$ of that residue equal to $1$, such that $T$ lies in the valuation subring of every place $P$ of $(C_i).\mathrm{dom}$ above $Q$ with $P$-value of $T$ in the maximal ideal of $A$, and such that for each $c$ in the maximal ideal there is exactly one such $P$ above $Q$ with $P.\mathrm{evalAt}\,T=c$; and assume the genus identity $g(F/L)+n=\sum_i g(\bar F_i/\kappa)+m+1$ for the finrank-of-$H^1(0)$ genus. With $F$ a curve over $L$ and each $\bar F_i$ a curve over $\kappa$, essentially of finite type, let $D_{\mathrm{an}}$ be a divisor of $F$ (a finitely supported $\mathbb Z$-valued function on places) each of whose support points $Q$ lies in some annulus domain with $Q.\mathrm{evalAt}$ of that annulus parameter equal to $u\pi^{d}$ for some unit $u$ and some $d\in\mathbb N$, and suppose that for every edge $e$ and depth $d$, and every finite set $S$ of places characterised as consisting exactly of the support points of $D_{\mathrm{an}}$ lying in $\mathrm{An}_e$ at depth $d$ in this sense, the sum of $D_{\mathrm{an}}$ over $S$ vanishes. Then there exist a nonzero $f\in F$ and a divisor $D_f$ with $D_f(Q)=Q.\mathrm{ord}(f)$ at every place $Q$, such that $D_f$ agrees with $D_{\mathrm{an}}$ at every place of every annulus domain, and divisors $D_0,\dots,D_{n-1}$ with $D_f-D_{\mathrm{an}}=\sum_i D_i$, each $D_i$ supported in $(C_i).\mathrm{dom}$ and of degree $0$.
--
--   This is the zero-potential ("compact") case of the lifting of principal divisors from the dual graph of a semistable covering to principal divisors of $F$, in the tradition of Raynaud's and Bosch–Lütkebohmert's uniformisation of curves and abelian varieties: a divisor on the lattice points of the annuli whose signed count on each lattice circle vanishes is cut out exactly, along the annuli, by a global function, the discrepancy being a degree-zero divisor supported on the charts; no multidegree map or graph Laplacian occurs, the balance condition being stated circle by circle. It is used, together with the two-point statement for a pair of lattice places of one annulus at equal depth and a fibrewise pair decomposition of finitely supported functions, in the further lifting result [`AlgebraicCurve.exists_ne_zero_ord_eq_of_forall_eq_zero_of_semistableCovering_of_discFibres_of_rankOne`](thm.html#AlgebraicCurve.exists_ne_zero_ord_eq_of_forall_eq_zero_of_semistableCovering_of_discFibres_of_rankOne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_ne_zero_ord_eq_of_depthMass_eq_zero_of_semistableCovering_of_rankOne.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_ne_zero_ord_eq_of_depthMass_eq_zero_of_semistableCovering_of_rankOne
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
    (Dan : Divisor L F)
    (hDan : ∀ Q ∈ Dan.support, ∃ e, Q ∈ (An e).dom ∧ ∃ (d : ℕ) (u : Aˣ) (h : Q.evalAt (An e).param ∈ A),
      (⟨Q.evalAt (An e).param, h⟩ : A) = u * π ^ d)
    (hmass : ∀ (e : Fin m) (d : ℕ), ∀ S : Finset (Place L F),
      (∀ Q, Q ∈ S ↔ Q ∈ Dan.support ∧ Q ∈ (An e).dom ∧
        ∃ (u : Aˣ) (h : Q.evalAt (An e).param ∈ A), (⟨Q.evalAt (An e).param, h⟩ : A) = u * π ^ d) →
      (S.sum fun Q => Dan Q) = 0)
    :
    ∃ (f : F) (Df : Divisor L F), f ≠ 0 ∧ (∀ Q, Df Q = Q.ord f) ∧
      (∀ e, ∀ Q ∈ (An e).dom, Df Q = Dan Q) ∧
      ∃ Di : Fin n → Divisor L F, Df - Dan = ∑ i, Di i ∧
        (∀ i, ∀ Q ∈ (Di i).support, Q ∈ (C i).dom) ∧ ∀ i, Divisor.degree (Di i) = 0 := by sorry
