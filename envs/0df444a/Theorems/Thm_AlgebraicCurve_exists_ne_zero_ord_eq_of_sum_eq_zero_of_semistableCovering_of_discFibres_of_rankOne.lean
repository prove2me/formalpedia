-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_ne_zero_ord_eq_of_sum_eq_zero_of_semistableCovering_of_discFibres_of_rankOne
-- name    : AlgebraicCurve.exists_ne_zero_ord_eq_of_sum_eq_zero_of_semistableCovering_of_discFibres_of_rankOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/cd9b6fe8-fc1d-54aa-9e78-0cb84f562414
-- title:
--   Lifting prescribed annulus divisors and Laplacian degrees on semistable coverings
-- statement:
--   Let $L$ be an algebraically closed field, $A\subseteq L$ a valuation subring, and $\pi\in A$ a nonzero element of the maximal ideal; assume $A$ has rank one in the form: for every $x\in L^{\times}$ and every $y$ in the maximal ideal there is $N$ with $A.\mathrm{valuation}(y^{N})\le A.\mathrm{valuation}(x)$. Let $F$ be a field extension of $L$, let $n,m\in\mathbb{N}$, and let $\bar F_i$ ($i<n$) be fields over the residue field $\kappa$ of $A$, all of whose places are rational (the structure map to the residue field of the place is surjective). Given component charts $C_i$ of $F$ over $\bar F_i$ relative to $A$, with all places in $(C_i).\mathrm{dom}$ rational, annuli $\mathrm{An}_e,\mathrm{An}'_e$ ($e<m$) with $(\mathrm{An}'_e).\mathrm{dom}=(\mathrm{An}_e).\mathrm{dom}$, equal moduli, modulus nonzero in $L$ and product of parameters equal to the image of the modulus, widths $w_e$ with modulus $u\pi^{w_e}$ for some unit $u$, source and target indices $\mathrm{src}(e),\mathrm{tgt}(e)$ and node places $x_s(e),x_t(e)$ such that $\mathrm{An}_e$ is attached to $C_{\mathrm{src}(e)}$ at $x_s(e)$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}(e)}$ at $x_t(e)$; assume every node of every chart is hit by exactly one of the $2m$ half-edges $(\mathrm{src}(e),x_s(e))$, $(\mathrm{tgt}(e),x_t(e))$, that the places of $F$ over $L$ are partitioned by the chart domains and the annulus domains (each place lying in exactly one of them and in no set of the other kind), that for each $i$ and each non-node place $Q$ of $\bar F_i$ there is $T\in (C_i).\mathrm{integers}$ whose residue is nonzero with $\mathrm{ord}_Q=1$, which lies in every place of the fibre over $Q$ with $\mathrm{evalAt}$ in the maximal ideal of $A$, and which takes each value $c$ in the maximal ideal at exactly one place of that fibre, and that $\mathrm{genusFF}(L,F)+n=\sum_i\mathrm{genusFF}(\kappa,\bar F_i)+m+1$; finally $F/L$ and each $\bar F_i/\kappa$ are curves in the sense of `IsCurveOver` and essentially of finite type. Put $V=\{0,\dots,n-1\}\sqcup\bigsqcup_e\{0,\dots,w_e-2\}$, let each pair $(e,d)$ with $d<w_e$ be an edge with endpoints $\mathrm{inl}(\mathrm{src}\,e)$ or $\mathrm{inr}(e,d-1)$ and $\mathrm{inl}(\mathrm{tgt}\,e)$ or $\mathrm{inr}(e,d)$ (so each annulus is subdivided into $w_e$ edges through $w_e-1$ interior vertices), and let $\mathrm{lap}(v)\in\mathbb{Z}^{V}$ be the corresponding Laplacian row, the sum over edges of $\delta_v-\delta_{\text{other end}}$ for each incidence of $v$. Then for every additive map $\mu:\mathrm{Divisor}(L,F)\to\mathbb{Z}^{V}$ sending a place $P\in (C_i).\mathrm{dom}$ to $\delta_{\mathrm{inl}\,i}$, sending $P\in(\mathrm{An}_e).\mathrm{dom}$ with $P.\mathrm{evalAt}$ of the annulus parameter equal to $u\pi^{d}$, $0<d<w_e$, to $\delta_{\mathrm{inr}(e,d-1)}$, and sending $P\in(\mathrm{An}_e).\mathrm{dom}$ whose parameter evaluation is of no such form to $0$: for every $c\in\mathbb{Z}^{V}$ and every divisor $D_{\mathrm{an}}$ supported at places lying in some annulus domain with parameter evaluation of the form $u\pi^{d}$, such that $\mu(D_{\mathrm{an}})$ and $\sum_u c_u\,\mathrm{lap}(u)$ agree at every interior vertex, there exist $f\in F$ nonzero and a divisor $D_f$ with $D_f(P)=P.\mathrm{ord}(f)$ for all places $P$, with $D_f=D_{\mathrm{an}}$ at every place of every annulus domain, and with $\mu(D_f)$ agreeing with $\sum_u c_u\,\mathrm{lap}(u)$ at every vertex $\mathrm{inl}\,i$.
--
--   This is the lifting step from tropical to algebraic data on a semistable covering: a divisor prescribed on the annuli, whose interior-vertex multidegrees come from a Laplacian (principal tropical divisor), is realised as the divisor of a function whose component multidegrees are the prescribed Laplacian values. It is obtained from the companion statement computing multidegrees of functions as Laplacian sums together with the vanishing case, and feeds the description of divisor classes and component groups for semistable models used downstream.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_ne_zero_ord_eq_of_sum_eq_zero_of_semistableCovering_of_discFibres_of_rankOne.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem
    AlgebraicCurve.exists_ne_zero_ord_eq_of_sum_eq_zero_of_semistableCovering_of_discFibres_of_rankOne
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
    :
    let V := Fin n ⊕ (Σ e : Fin m, Fin (w e - 1))
    let ends : (Σ e : Fin m, Fin (w e)) → V × V := fun ε =>
      (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
       if h1 : ε.2.1 + 1 = w ε.1 then Sum.inl (tgt ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩)
    let lap : V → (V → ℤ) := fun v => ∑ ε : Σ e : Fin m, Fin (w e),
      ((if (ends ε).1 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ) else 0) +
       (if (ends ε).2 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).1 1 : V → ℤ) else 0))
    ∀ μ : Divisor L F →+ (V → ℤ),
      (∀ i, ∀ P ∈ (C i).dom, μ (Finsupp.single P 1) = Pi.single (Sum.inl i) 1) →
      (∀ e, ∀ P ∈ (An e).dom, ∀ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
        (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d → ∀ (hd0 : 0 < d) (hdw : d < w e),
          μ (Finsupp.single P 1) = Pi.single (Sum.inr ⟨e, ⟨d - 1, by omega⟩⟩) 1) →
      (∀ e, ∀ P ∈ (An e).dom,
        (¬ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
          (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) → μ (Finsupp.single P 1) = 0) →
      ∀ (c : V → ℤ) (Dan : Divisor L F),
        (∀ P ∈ Dan.support, ∃ e, P ∈ (An e).dom ∧ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
          (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) →
        (∀ v : Σ e : Fin m, Fin (w e - 1), μ Dan (Sum.inr v) = (∑ u, c u • lap u) (Sum.inr v)) →
        ∃ (f : F) (Df : Divisor L F), f ≠ 0 ∧ (∀ P, Df P = P.ord f) ∧
          (∀ e, ∀ Q ∈ (An e).dom, Df Q = Dan Q) ∧ ∀ i, μ Df (Sum.inl i) = (∑ u, c u • lap u) (Sum.inl i) := by sorry
