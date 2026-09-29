-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_ne_zero_apply_ord_eq_sum_lap_of_semistableCovering_of_discFibres_of_rankOne_of_width_one
-- name    : AlgebraicCurve.exists_ne_zero_apply_ord_eq_sum_lap_of_semistableCovering_of_discFibres_of_rankOne_of_width_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/af864fe6-1e16-53a2-a852-a567311b5bc3
-- title:
--   Potential lifting on a semistable covering by width-one annuli
-- statement:
--   Let $L$ be an algebraically closed field, $A$ a valuation subring of $L$ and $\pi$ a nonzero element of its maximal ideal, and assume the rank-one condition that for every $x \in L^{\times}$ and every $y$ in the maximal ideal some power $y^{n}$ has valuation at most that of $x$. Let $F$ be a field extension of $L$ which is a curve over $L$ (finitely supported principal divisors of degree zero, finite residue extensions, $\Omega_{F/L}$ free of rank one) and essentially of finite type, and let $\bar{F}_i$, $i \in \mathrm{Fin}\ n$, be curve fields over the residue field of $A$, all of whose places are rational. Given component charts $C_i$ with all places of $C_i.\mathrm{dom}$ rational, and annuli $\mathrm{An}_e$, $\mathrm{An}'_e$, $e \in \mathrm{Fin}\ m$, with source and target indices $\mathrm{src}\,e$, $\mathrm{tgt}\,e$ and node points $x_s(e)$, $x_t(e)$, assume: each pair $\mathrm{An}_e$, $\mathrm{An}'_e$ has the same domain and the same nonzero modulus, with the product of their parameters equal to the image of that modulus; each modulus is a unit times $\pi^{w(e)}$; every width $w(e)$ equals $1$; $\mathrm{An}_e$ is attached to $C_{\mathrm{src}\,e}$ at $x_s(e)$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}\,e}$ at $x_t(e)$; every node of every chart is an endpoint of an annulus, and the endpoint assignment $\mathrm{Fin}\ m \oplus \mathrm{Fin}\ m \to \Sigma_j\,\mathrm{Place}$ hits each node at most once; the chart and annulus domains partition the places of $F$ (each place lies in exactly one chart domain and no annulus domain, or in exactly one annulus domain and no chart domain); over every non-node point $Q$ of a chart the fibre is a disc, i.e. there is $T$ in the chart's integers whose residue is nonzero with $\mathrm{ord}_Q = 1$, lying in the valuation ring of every $P$ over $Q$ with $P$-value in the maximal ideal of $A$, and such that every element of the maximal ideal is the value of $T$ at exactly one such $P$; and the genus identity $g(F) + n = \sum_i g(\bar{F}_i) + m + 1$. Put $V = \mathrm{Fin}\ n \oplus \Sigma_e\,\mathrm{Fin}(w(e)-1)$ (here the second summand is empty, so $V$ is the set of charts), let $\mathrm{ends}$ send the segment $(e,d)$ to its two neighbouring vertices and let $\mathrm{lap}$ be the associated graph Laplacian on $\mathbb{Z}^{V}$. Then for every additive map $\mu$ from divisors of $F/L$ to $\mathbb{Z}^{V}$ which sends a place of $C_i.\mathrm{dom}$ to the standard vector at $i$, a place of $\mathrm{An}_e.\mathrm{dom}$ whose parameter value is a unit times $\pi^{d}$ with $0 < d < w(e)$ to the standard vector at the lattice vertex $(e,d-1)$, and a place of $\mathrm{An}_e.\mathrm{dom}$ whose parameter value is not of the form (unit)$\cdot\pi^{d}$ to $0$, and for every $c : V \to \mathbb{Z}$, there are a nonzero $g \in F$ and a divisor $D_g$ with $D_g(P) = \mathrm{ord}_P(g)$ for all $P$, whose support consists only of places lying in some chart domain or in some annulus domain at integral depth, and with $\mu(D_g) = \sum_{u} c(u)\,\mathrm{lap}(u)$.
--
--   This is the width-one case of the potential-lifting step for semistable coverings: every integer potential on the dual graph of the covering is realised as the Laplacian multidegree of a nonzero function, the places themselves being unconstrained apart from their location. It is used by the general-width statement [`AlgebraicCurve.exists_ne_zero_apply_ord_eq_sum_lap_of_semistableCovering_of_discFibres_of_rankOne`](thm.html#AlgebraicCurve.exists_ne_zero_apply_ord_eq_sum_lap_of_semistableCovering_of_discFibres_of_rankOne), and rests on the width-one unit-normalisation and Laplacian-computation lemmas for semistable coverings together with Riemann–Roch over an algebraically closed constant field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_ne_zero_apply_ord_eq_sum_lap_of_semistableCovering_of_discFibres_of_rankOne_of_width_one.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_ne_zero_apply_ord_eq_sum_lap_of_semistableCovering_of_discFibres_of_rankOne_of_width_one
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
    (hw1 : ∀ e, w e = 1)
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
      ∀ c : V → ℤ, ∃ (g : F) (Dg : Divisor L F), g ≠ 0 ∧ (∀ P, Dg P = P.ord g) ∧
        (∀ P ∈ Dg.support, (∃ i, P ∈ (C i).dom) ∨
          ∃ e, P ∈ (An e).dom ∧ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
            (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) ∧
        μ Dg = ∑ u, c u • lap u := by sorry
