-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableCovering_exists_widthOne_covering_equiv_of_discFibres_of_rankOne
-- name    : AlgebraicCurve.SemistableCovering.exists_widthOne_covering_equiv_of_discFibres_of_rankOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/9b7289c9-ceed-59bf-9309-b62ab387c843
-- title:
--   Width-one refinement of a semistable covering, reindexed
-- statement:
--   Let $L$ be an algebraically closed field, $A\subseteq L$ a valuation subring, $\pi\in A$ a nonzero element of the maximal ideal, and assume the rank-one condition that for every $x\in L^{\times}$ and every $y$ in the maximal ideal of $A$ some power $y^{n}$ has valuation at most that of $x$; let $F$ be a field extension of $L$ which is a curve over $L$ and essentially of finite type, let $k$ be the residue field of $A$, and let $\bar F_{i}$ ($i<n$) be fields over $k$, each a curve over $k$ and essentially of finite type. The covering data consist of: component charts $C_i$ over $\bar F_i$, annuli $An_e,An'_e$ ($e<m$) with end maps $\mathrm{src},\mathrm{tgt}:\mathrm{Fin}\,m\to\mathrm{Fin}\,n$, nodes $xs_e,xt_e$ and widths $w_e$, subject to the hypotheses (summarised here): all places of each $\bar F_i$ over $k$ and all places in each $(C_i).\mathrm{dom}$ are rational; $An'_e$ and $An_e$ share domain and modulus, the modulus is nonzero in $L$ and the two parameters multiply to the image of the modulus; the modulus of $An_e$ is a unit times $\pi^{w_e}$; $An_e$ is attached to $C_{\mathrm{src}\,e}$ at $xs_e$ and $An'_e$ to $C_{\mathrm{tgt}\,e}$ at $xt_e$; every node of every chart is an end of an annulus, and is so for exactly one of the $2m$ ends; every place of $F/L$ lies either in exactly one chart domain and no annulus domain, or in exactly one annulus domain and no chart domain; the disc-fibre condition that for each $i$ and each non-node place $Q$ of $\bar F_i$ there is $T\in (C_i).\mathrm{integers}$ with nonzero residue, $\operatorname{ord}_Q$ of that residue equal to $1$, with $T$ integral and $P.\mathrm{evalAt}\,T$ in the maximal ideal of $A$ at every $P$ in the chart domain above $Q$, and with exactly one such $P$ realising each prescribed value $c$ in the maximal ideal; and the genus identity $g(F/L)+n=\sum_i g(\bar F_i/k)+m+1$. Put $V=\mathrm{Fin}\,n\sqcup\bigl(\Sigma_e\,\mathrm{Fin}(w_e-1)\bigr)$ and let $\mathrm{ends}$ send an edge $(e,d)\in\Sigma_e\,\mathrm{Fin}\,w_e$ to the pair whose first entry is the chart $\mathrm{src}\,e$ if $d=0$ and the lattice vertex $(e,d-1)$ otherwise, and whose second entry is the chart $\mathrm{tgt}\,e$ if $d+1=w_e$ and the lattice vertex $(e,d)$ otherwise. The conclusion asserts the existence of $n',m'\in\mathbb N$, bijections $eV:V\simeq \mathrm{Fin}\,n'$ and $eE:\Sigma_e\,\mathrm{Fin}\,w_e\simeq\mathrm{Fin}\,m'$, fields $\bar F'_{i'}$ with $k$-algebra structures, component charts $C'_{i'}$, annuli $An_{1,e'},An'_{1,e'}$, end maps $\mathrm{src}',\mathrm{tgt}'$ and nodes $xs',xt'$ satisfying all of the above hypotheses for the primed data — with every modulus of the form $u\pi^{1}$, the genus identity $g(F/L)+n'=\sum_{i'}g(\bar F'_{i'}/k)+m'+1$, and each $\bar F'_{i'}$ a curve over $k$ essentially of finite type — and, in addition, transport clauses: $C'_{eV(\mathrm{inl}\,i)}$ has the same domain and the same ring of integers as $C_i$; for a lattice vertex $v=(e,d)$ the domain of $C'_{eV(\mathrm{inr}\,v)}$ is the set of $P\in (An_e).\mathrm{dom}$ whose value $P.\mathrm{evalAt}$ of the parameter of $An_e$ equals a unit times $\pi^{d+1}$; for an edge $\varepsilon=(e,d)$ the domain of $An_{1,eE(\varepsilon)}$ is the set of $P\in(An_e).\mathrm{dom}$ with $v(\pi^{d+1})<v(P.\mathrm{evalAt}(\text{param of }An_e))<v(\pi^{d})$ and its parameter is the parameter of $An_e$ divided by the image of $\pi^{d}$; and $\mathrm{src}'(eE\,\varepsilon)$, $\mathrm{tgt}'(eE\,\varepsilon)$ are the $eV$-images of the two ends of $\varepsilon$.
--
--   This is the packaging step of the refinement theory for semistable coverings of a one-variable function field along a rank-one valuation subring: a covering whose annuli have arbitrary widths $w_e$ is replaced by one all of whose annuli have width one, indexed by the subdivision of the incidence graph in which each edge is cut into $w_e$ edges with $w_e-1$ new vertices, the two-sorted index sets being transported to the $\mathrm{Fin}\,n'$, $\mathrm{Fin}\,m'$ frame. It is obtained from the width-one refinement [`AlgebraicCurve.SemistableCovering.exists_circleCharts_and_bands_width_one_of_discFibres_of_rankOne`](thm.html#AlgebraicCurve.SemistableCovering.exists_circleCharts_and_bands_width_one_of_discFibres_of_rankOne) and feeds the potential-theoretic (chip-firing) computation [`AlgebraicCurve.exists_ne_zero_apply_ord_eq_sum_lap_of_semistableCovering_of_discFibres_of_rankOne`](thm.html#AlgebraicCurve.exists_ne_zero_apply_ord_eq_sum_lap_of_semistableCovering_of_discFibres_of_rankOne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableCovering_exists_widthOne_covering_equiv_of_discFibres_of_rankOne.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open AlgebraicCurve

theorem AlgebraicCurve.SemistableCovering.exists_widthOne_covering_equiv_of_discFibres_of_rankOne
    {L : Type u} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type*) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type v) [∀ i, Field (Fbar i)]
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
    ∃ (n' m' : ℕ) (eV : V ≃ Fin n') (eE : (Σ e : Fin m, Fin (w e)) ≃ Fin m')
      (Fbar' : Fin n' → Type (max u v)) (instF : ∀ i, Field (Fbar' i))
      (instA : ∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar' i))
      (C' : ∀ i, ComponentChart A F (Fbar' i)) (An₁ An₁' : Fin m' → Annulus A F) (src' tgt' : Fin m' → Fin n')
      (xs' : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar' (src' e)))
      (xt' : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar' (tgt' e))),

      (∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar' i), Q.IsRational) ∧
      (∀ i, ∀ P ∈ (C' i).dom, P.IsRational) ∧
      (∀ e, (An₁' e).dom = (An₁ e).dom ∧ (An₁' e).modulus = (An₁ e).modulus ∧
      ((An₁ e).modulus : L) ≠ 0 ∧
      (An₁' e).param * (An₁ e).param = algebraMap L F ((An₁ e).modulus : L)) ∧
      (∀ e, ∃ u : Aˣ, (An₁ e).modulus = u * π ^ 1) ∧
      (∀ e, (An₁ e).IsAttached (C' (src' e)) (xs' e) ∧ (An₁' e).IsAttached (C' (tgt' e)) (xt' e)) ∧
      ((∀ i, ∀ x ∈ (C' i).nodes, ∃ e,
        (⟨src' e, xs' e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar' j)) = ⟨i, x⟩ ∨
        (⟨tgt' e, xt' e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar' j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C' i).nodes, ∀ E E' : Fin m' ⊕ Fin m',
        Sum.elim (fun e => (⟨src' e, xs' e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar' j)))
          (fun e => ⟨tgt' e, xt' e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src' e, xs' e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar' j)))
          (fun e => ⟨tgt' e, xt' e⟩) E' = ⟨i, x⟩ → E = E')) ∧
      (∀ P : Place L F,
      (∃ i, P ∈ (C' i).dom ∧ (∀ j, P ∈ (C' j).dom → j = i) ∧ ∀ e, P ∉ (An₁ e).dom) ∨
      (∃ e, P ∈ (An₁ e).dom ∧ (∀ e', P ∈ (An₁ e').dom → e' = e) ∧ ∀ i, P ∉ (C' i).dom)) ∧
      (∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar' i), Q ∉ (C' i).nodes →
      ∃ (T : F) (hT : T ∈ (C' i).integers), (C' i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C' i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C' i).dom, (C' i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C' i).dom ∧ (C' i).placeMap P = Q ∧ P.evalAt T = c) ∧
      (genusFF L F + n' = (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar' i)) + m' + 1) ∧
      (∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar' i)) ∧
      (∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar' i)) ∧

      (∀ i : Fin n, (C' (eV (Sum.inl i))).dom = (C i).dom ∧ (C' (eV (Sum.inl i))).integers = (C i).integers) ∧
      (∀ v : (Σ e : Fin m, Fin (w e - 1)), (C' (eV (Sum.inr v))).dom =
        {P | P ∈ (An v.1).dom ∧ ∃ (u : Aˣ) (h : P.evalAt (An v.1).param ∈ A),
          (⟨P.evalAt (An v.1).param, h⟩ : A) = u * π ^ (v.2.1 + 1)}) ∧
      (∀ ε : (Σ e : Fin m, Fin (w e)), (An₁ (eE ε)).dom =
        {P | P ∈ (An ε.1).dom ∧
          A.valuation (((π : A) : L) ^ (ε.2.1 + 1)) < A.valuation (P.evalAt (An ε.1).param) ∧
          A.valuation (P.evalAt (An ε.1).param) < A.valuation (((π : A) : L) ^ ε.2.1)} ∧
        (An₁ (eE ε)).param = (algebraMap L F (((π : A) : L) ^ ε.2.1))⁻¹ * (An ε.1).param) ∧
      (∀ ε : (Σ e : Fin m, Fin (w e)), src' (eE ε) = eV (ends ε).1 ∧ tgt' (eE ε) = eV (ends ε).2) := by sorry
