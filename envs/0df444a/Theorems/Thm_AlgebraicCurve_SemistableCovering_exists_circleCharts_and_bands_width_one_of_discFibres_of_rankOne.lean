-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableCovering_exists_circleCharts_and_bands_width_one_of_discFibres_of_rankOne
-- name    : AlgebraicCurve.SemistableCovering.exists_circleCharts_and_bands_width_one_of_discFibres_of_rankOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/fca8e5a9-1d5d-5f48-a2b2-61cf6c3b5fec
-- title:
--   Refining a semistable covering into width-one annuli
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring, and $\pi \in A$ a nonzero element of the maximal ideal; assume $A$ has archimedean value group in the sense that for every $x \in L^{\times}$ and every $y$ in the maximal ideal of $A$ some power satisfies $A.\mathrm{valuation}(y^{n}) \le A.\mathrm{valuation}(x)$. Let $F$ be a field over $L$ which is a curve over $L$ and essentially of finite type, let $k$ denote the residue field of $A$, and let $\bar F_{1},\dots,\bar F_{n}$ be curves over $k$, essentially of finite type, all of whose places are rational. The data are: for each $i$ a `ComponentChart` $C_i$ for $A$, $F$, $\bar F_i$ (a valuation subring of $F$ with surjective reduction onto $\bar F_i$ with kernel the maximal ideal, a set `dom` of places of $F/L$, a finite set `nodes` of places of $\bar F_i/k$, and a reduction map `placeMap` on places, subject to the structure's axioms), all places of $(C_i).\mathrm{dom}$ being rational; annuli $\mathrm{An}_e, \mathrm{An}'_e$ ($e \in \mathrm{Fin}\,m$) with $\mathrm{An}'_e$ the reflected partner of $\mathrm{An}_e$ (same domain, same nonzero modulus, and the product of the two parameters equal to the image of the modulus); edge endpoints $\mathrm{src}\,e, \mathrm{tgt}\,e$ with nodes $x_{s}(e)$ on $\bar F_{\mathrm{src}\,e}$ and $x_{t}(e)$ on $\bar F_{\mathrm{tgt}\,e}$; widths $w_e$ with $(\mathrm{An}_e).\mathrm{modulus} = u\,\pi^{w_e}$ for some unit $u$ of $A$; attachments $\mathrm{An}_e \sim (C_{\mathrm{src}\,e}, x_s(e))$ and $\mathrm{An}'_e \sim (C_{\mathrm{tgt}\,e}, x_t(e))$ in the sense of `IsAttached` (the node lies in `nodes`, the annulus parameter is integral on the chart with $\mathrm{ord}$ of its reduction equal to $1$ at that node, and every chart function with nonzero reduction and vanishing order along the annulus becomes, after the indicated normalisation by a power of the parameter, a unit of $A$ at each place of the annulus); the condition that every node of every chart is the end of exactly one of the $2m$ annulus ends $\langle \mathrm{src}\,e, x_s(e)\rangle$, $\langle \mathrm{tgt}\,e, x_t(e)\rangle$; the covering condition that every place of $F/L$ lies in exactly one chart domain and no annulus domain, or in exactly one annulus domain and no chart domain; a disc-fibre condition, stating that for each $i$ and each place $Q$ of $\bar F_i/k$ outside $(C_i).\mathrm{nodes}$ there is a chart function $T$ with nonzero reduction of order $1$ at $Q$, integral with value in the maximal ideal of $A$ at every place of the chart domain above $Q$, and such that every $c$ in the maximal ideal of $A$ is the value of $T$ at exactly one place of the chart domain above $Q$; and the genus identity $\mathrm{genusFF}(L,F) + n = \sum_i \mathrm{genusFF}(k, \bar F_i) + m + 1$. The conclusion asserts the existence of component charts $Cc_{e,d}$ for $A$, $F$, $k(X)$ indexed by $e \in \mathrm{Fin}\,m$ and $d \in \mathrm{Fin}(w_e - 1)$, a place $Q_{\infty}$ of $k(X)/k$ with $X \notin Q_{\infty}$'s valuation subring, and annuli $B_{e,d}, B'_{e,d}$ indexed by $e$ and $d \in \mathrm{Fin}(w_e)$, such that: the domain of $Cc_{e,d}$ is the set of places $P$ of $\mathrm{An}_e$ with $P.\mathrm{evalAt}$ of the parameter equal to a unit times $\pi^{d+1}$; its nodes are $\{\mathrm{placeOfPoint}\,0, Q_{\infty}\}$; the function $\pi^{-(d+1)}$ times the parameter of $\mathrm{An}_e$ is integral on $Cc_{e,d}$ with reduction $X$; its `placeMap` sends $P$ to $\mathrm{placeOfPoint}$ of the residue of $\pi^{-(d+1)} P.\mathrm{evalAt}$(parameter); the domain of $B_{e,d}$ is the band of places of $\mathrm{An}_e$ with $A.\mathrm{valuation}(\pi^{d+1}) < A.\mathrm{valuation}(P.\mathrm{evalAt}\ \text{parameter}) < A.\mathrm{valuation}(\pi^{d})$, its parameter is $\pi^{-d}$ times that of $\mathrm{An}_e$, $B'_{e,d}$ is the reflected partner of $B_{e,d}$, the moduli satisfy $(B_{e,d}).\mathrm{modulus}\cdot \pi^{w_e-1} = (\mathrm{An}_e).\mathrm{modulus}$ in $L$ and each equals a unit times $\pi^{1}$; $B_{e,0}$ is attached to $(C_{\mathrm{src}\,e}, x_s(e))$ when $w_e > 0$, $B'_{e,d}$ with $d+1 = w_e$ is attached to $(C_{\mathrm{tgt}\,e}, x_t(e))$, $B_{e,d}$ with $d>0$ is attached to $(Cc_{e,d-1}, \mathrm{placeOfPoint}\,0)$, and $B'_{e,d}$ with $d+1 < w_e$ is attached to $(Cc_{e,d}, Q_{\infty})$; every place of $F/L$ lies in exactly one of the domains of the $C_i$, the $Cc_{e,d}$ and the $B_{e,d}$, and in no domain of the other two families; the same disc-fibre condition holds for each $Cc_{e,d}$; every place of $k(X)/k$ is rational and every place in a domain $(Cc_{e,d}).\mathrm{dom}$ is rational; and the refined genus identity $\mathrm{genusFF}(L,F) + (n + \sum_e (w_e-1)) = \sum_i \mathrm{genusFF}(k,\bar F_i) + \sum_{(e,d)} \mathrm{genusFF}(k,k(X)) + \sum_e w_e + 1$ holds.
--
--   This is the lattice-refinement step for semistable coverings of a one-variable function field along a rank-one valuation subring: each annulus of width $w$ is cut at the $w-1$ lattice circles $|z| = |\pi|^{d}$, which become genus-zero component charts with reduced field $k(X)$ and two nodes $X=0$, $X=\infty$, leaving $w$ annuli of width one between them, with the dual graph subdivided accordingly and the genus identity preserved. It is used by [`AlgebraicCurve.SemistableCovering.exists_widthOne_covering_equiv_of_discFibres_of_rankOne`](thm.html#AlgebraicCurve.SemistableCovering.exists_widthOne_covering_equiv_of_discFibres_of_rankOne), which packages the refined data as a covering all of whose annuli have width one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableCovering_exists_circleCharts_and_bands_width_one_of_discFibres_of_rankOne.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.RationalFunctionField

open Classical in

theorem AlgebraicCurve.SemistableCovering.exists_circleCharts_and_bands_width_one_of_discFibres_of_rankOne
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
    ∃ (Cc : (Σ e : Fin m, Fin (w e - 1)) → ComponentChart A F (RatFunc (IsLocalRing.ResidueField A)))
      (Qinf : Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)))
      (B B' : (Σ e : Fin m, Fin (w e)) → Annulus A F),

      (RatFunc.X : RatFunc (IsLocalRing.ResidueField A)) ∉ Qinf.toValuationSubring ∧

      (∀ v, (Cc v).dom = {P | P ∈ (An v.1).dom ∧ ∃ (u : Aˣ) (h : P.evalAt (An v.1).param ∈ A),
          (⟨P.evalAt (An v.1).param, h⟩ : A) = u * π ^ (v.2.1 + 1)}) ∧
      (∀ v, (Cc v).nodes = {placeOfPoint (IsLocalRing.ResidueField A) 0, Qinf}) ∧
      (∀ v, ∃ h : (algebraMap L F (((π : A) : L) ^ (v.2.1 + 1)))⁻¹ * (An v.1).param ∈ (Cc v).integers,
          (Cc v).residue ⟨_, h⟩ = (RatFunc.X : RatFunc (IsLocalRing.ResidueField A))) ∧
      (∀ v, ∀ P ∈ (Cc v).dom, ∀ h : (((π : A) : L) ^ (v.2.1 + 1))⁻¹ * P.evalAt (An v.1).param ∈ A,
          (Cc v).placeMap P = placeOfPoint (IsLocalRing.ResidueField A) (IsLocalRing.residue A ⟨_, h⟩)) ∧

      (∀ ε, (B ε).dom = {P | P ∈ (An ε.1).dom ∧
          A.valuation (((π : A) : L) ^ (ε.2.1 + 1)) < A.valuation (P.evalAt (An ε.1).param) ∧
          A.valuation (P.evalAt (An ε.1).param) < A.valuation (((π : A) : L) ^ ε.2.1)}) ∧
      (∀ ε, (B ε).param = (algebraMap L F (((π : A) : L) ^ ε.2.1))⁻¹ * (An ε.1).param) ∧
      (∀ ε, (B' ε).dom = (B ε).dom ∧ (B' ε).modulus = (B ε).modulus ∧ ((B ε).modulus : L) ≠ 0 ∧
          (B' ε).param * (B ε).param = algebraMap L F ((B ε).modulus : L)) ∧
      (∀ ε, ((B ε).modulus : L) * ((π : A) : L) ^ (w ε.1 - 1) = ((An ε.1).modulus : L)) ∧
      (∀ ε, ∃ u : Aˣ, (B ε).modulus = u * π ^ 1) ∧

      (∀ e (h0 : 0 < w e), (B ⟨e, ⟨0, h0⟩⟩).IsAttached (C (src e)) (xs e)) ∧
      (∀ e (d : Fin (w e)), d.1 + 1 = w e → (B' ⟨e, d⟩).IsAttached (C (tgt e)) (xt e)) ∧
      (∀ e (d : Fin (w e)) (hd : 0 < d.1),
          (B ⟨e, d⟩).IsAttached (Cc ⟨e, ⟨d.1 - 1, by have := d.2; omega⟩⟩) (placeOfPoint (IsLocalRing.ResidueField A) 0)) ∧
      (∀ e (d : Fin (w e)) (hd : d.1 + 1 < w e),
          (B' ⟨e, d⟩).IsAttached (Cc ⟨e, ⟨d.1, by omega⟩⟩) Qinf) ∧

      (∀ P : Place L F,
        (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ (∀ v, P ∉ (Cc v).dom) ∧ ∀ ε, P ∉ (B ε).dom) ∨
        (∃ v, P ∈ (Cc v).dom ∧ (∀ v', P ∈ (Cc v').dom → v' = v) ∧ (∀ i, P ∉ (C i).dom) ∧ ∀ ε, P ∉ (B ε).dom) ∨
        (∃ ε, P ∈ (B ε).dom ∧ (∀ ε', P ∈ (B ε').dom → ε' = ε) ∧ (∀ i, P ∉ (C i).dom) ∧ ∀ v, P ∉ (Cc v).dom)) ∧

      (∀ v, ∀ Q : Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)), Q ∉ (Cc v).nodes →
        ∃ (T : F) (hT : T ∈ (Cc v).integers), (Cc v).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((Cc v).residue ⟨T, hT⟩) = 1 ∧
          (∀ P ∈ (Cc v).dom, (Cc v).placeMap P = Q → T ∈ P.toValuationSubring ∧
            ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
          ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
            ∃! P : Place L F, P ∈ (Cc v).dom ∧ (Cc v).placeMap P = Q ∧ P.evalAt T = c) ∧

      (∀ Q : Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)), Q.IsRational) ∧ (∀ v, ∀ P ∈ (Cc v).dom, P.IsRational) ∧

      (genusFF L F + (n + ∑ e, (w e - 1)) =
        (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + (∑ v : (Σ e : Fin m, Fin (w e - 1)), genusFF (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A))) +
          (∑ e, w e) + 1) := by sorry
