-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableCovering_exists_ne_zero_ord_eq_single_sub_single_mapDomain_placeMap_mem_principal_of_valuation_eq_of_rankOne
-- name    : AlgebraicCurve.SemistableCovering.exists_ne_zero_ord_eq_single_sub_single_mapDomain_placeMap_mem_principal_of_valuation_eq_of_rankOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/3842cda8-a39c-5276-8180-de539130603d
-- title:
--   Principal chartwise push-forwards for [P]-[P'] on one annulus
-- statement:
--   Fix an algebraically closed field $L$, a valuation subring $A \subseteq L$ and a nonzero $\pi$ in the maximal ideal of $A$, and assume the rank-one condition that for every nonzero $x \in L$ and every $y$ in the maximal ideal some power $y^n$ has valuation at most that of $x$. Let $F$ be a field extension of $L$, and let $\bar F_i$ ($i \in \mathrm{Fin}\,n$) be extensions of the residue field $\kappa = A/\mathfrak m$ all of whose places are rational (i.e. $\kappa$ surjects onto each residue field). The covering data consist of: component charts $C_i$ (a valuation subring of $F$ with a surjective residue map onto $\bar F_i$ with kernel the maximal ideal, a domain of places of $F/L$, a finite set of nodes in $\bar F_i$, and a reduction map `placeMap` on places, subject to the compatibilities in `ComponentChart`), all places of $\mathrm{dom}(C_i)$ being rational; annuli $\mathrm{An}_e, \mathrm{An}'_e$ ($e \in \mathrm{Fin}\,m$) with source and target indices $\mathrm{src}\,e, \mathrm{tgt}\,e$, nodes $x_s(e)$ on $\bar F_{\mathrm{src}\,e}$ and $x_t(e)$ on $\bar F_{\mathrm{tgt}\,e}$, and widths $w_e \in \mathbb N$; the pairing hypothesis that $\mathrm{An}'_e$ and $\mathrm{An}_e$ have the same domain and the same modulus, that this modulus is nonzero in $L$, and that the product of the two parameters is the image of the modulus; that the modulus of $\mathrm{An}_e$ is a unit times $\pi^{w_e}$; that $\mathrm{An}_e$ is attached to $C_{\mathrm{src}\,e}$ at $x_s(e)$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}\,e}$ at $x_t(e)$ in the sense of `IsAttached`; that every node of every chart is hit by exactly one of the $2m$ endpoint assignments $e \mapsto \langle \mathrm{src}\,e, x_s(e)\rangle$, $e \mapsto \langle \mathrm{tgt}\,e, x_t(e)\rangle$; that every place of $F/L$ lies either in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain; the disc hypothesis that for each $i$ and each non-node place $Q$ of $\bar F_i$ there is $T$ in the integers of $C_i$ whose residue is nonzero with $\mathrm{ord}_Q = 1$, lying in the valuation ring of every $P \in \mathrm{dom}(C_i)$ reducing to $Q$ with $P$-value in the maximal ideal of $A$, and such that every $c$ in the maximal ideal of $A$ is the value $P.\mathrm{evalAt}\,T$ for a unique such $P$; and the genus relation $\mathrm{genus}(F/L) + n = \sum_i \mathrm{genus}(\bar F_i/\kappa) + m + 1$. Both $F/L$ and each $\bar F_i/\kappa$ are curves in the sense of `IsCurveOver` and essentially of finite type. Finally fix an edge $e_0$ and places $P, P' \in \mathrm{dom}(\mathrm{An}_{e_0})$ at the same radius, that is, $P.\mathrm{evalAt}$ of the parameter is a unit of $A$ times $P'.\mathrm{evalAt}$ of the parameter, and assume this radius is rational over $\pi$: for some $N > 0$, $d$ and a unit $v$ one has $(P.\mathrm{evalAt}\,z)^N = v\pi^d$. The conclusion: there are a nonzero $f \in F$ and a divisor $D_f$ with $D_f(Q) = \mathrm{ord}_Q(f)$ for every place $Q$ of $F/L$, such that $D_f$ agrees with $[P]-[P']$ at every place lying in an annulus domain, together with divisors $D_i$ ($i \in \mathrm{Fin}\,n$) with $D_f - ([P]-[P']) = \sum_i D_i$, each $D_i$ supported in $\mathrm{dom}(C_i)$, and each push-forward $\mathrm{placeMap}_{i,*}D_i$ principal on $\bar F_i/\kappa$, i.e. equal to the divisor of some nonzero element of $\bar F_i$.
--
--   This is the sharpened form of the same-radius statement for a semistable covering: the class of $[P]-[P']$ on an annulus becomes, after subtracting a principal divisor supported away from the annuli, a sum of chart divisors whose reductions are principal on each component, so that its abelian part vanishes and only the toric coordinate across $e_0$ survives. It combines [`AlgebraicCurve.SemistableCovering.exists_ne_zero_ord_eq_single_sub_single_of_depth_eq_of_rankOne`](thm.html#AlgebraicCurve.SemistableCovering.exists_ne_zero_ord_eq_single_sub_single_of_depth_eq_of_rankOne) with the principality criterion [`AlgebraicCurve.mapDomain_placeMap_mem_principal_of_degree_eq_zero_of_forall_annulus_sum_eq_zero_of_prod_valuation_evalAt_zpow_eq_one`](thm.html#AlgebraicCurve.mapDomain_placeMap_mem_principal_of_degree_eq_zero_of_forall_annulus_sum_eq_zero_of_prod_valuation_evalAt_zpow_eq_one), and is used in the analysis of elements of the intersection of the kernels of the reduction maps attached to a semistable model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableCovering_exists_ne_zero_ord_eq_single_sub_single_mapDomain_placeMap_mem_principal_of_valuation_eq_of_rankOne.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem
    AlgebraicCurve.SemistableCovering.exists_ne_zero_ord_eq_single_sub_single_mapDomain_placeMap_mem_principal_of_valuation_eq_of_rankOne
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
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
    (e₀ : Fin m) (P P' : Place L F) (hP : P ∈ (An e₀).dom) (hP' : P' ∈ (An e₀).dom)
    (hrad : ∃ u : Aˣ, P.evalAt (An e₀).param = ((u : A) : L) * P'.evalAt (An e₀).param)
    (hrat : ∃ (N d : ℕ) (v : Aˣ), 0 < N ∧ (P.evalAt (An e₀).param) ^ N = ((v : A) : L) * (π : L) ^ d)
    :
    ∃ (f : F) (Df : Divisor L F), f ≠ 0 ∧ (∀ Q, Df Q = Q.ord f) ∧
      (∀ e, ∀ Q ∈ (An e).dom, Df Q = (Finsupp.single P 1 - Finsupp.single P' 1 : Divisor L F) Q) ∧
      ∃ Di : Fin n → Divisor L F, Df - (Finsupp.single P 1 - Finsupp.single P' 1) = ∑ i, Di i ∧
        (∀ i, ∀ Q ∈ (Di i).support, Q ∈ (C i).dom) ∧
        ∀ i, Finsupp.mapDomain (C i).placeMap (Di i) ∈
          Divisor.principal (K := IsLocalRing.ResidueField A) (F := Fbar i) := by sorry
