-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_add_sum_sub_sum_mem_principal_of_degree_add_sum_eq_zero_of_valuation_mul_prod_eq_of_lattice_of_semistableCovering_of_discFibres_of_rankOne
-- name    : AlgebraicCurve.exists_add_sum_sub_sum_mem_principal_of_degree_add_sum_eq_zero_of_valuation_mul_prod_eq_of_lattice_of_semistableCovering_of_discFibres_of_rankOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/b223fe88-fe8d-5831-9a1a-9142e36e4b10
-- title:
--   Tropically principal divisors are chart-representable in chart-degrees zero
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring, and $\pi$ a nonzero element of the maximal ideal of $A$; assume the rank-one condition that for every $x \in L^{\times}$ and every $y$ in the maximal ideal of $A$ some power $y^{n}$ satisfies $A.\mathrm{valuation}(y^{n}) \le A.\mathrm{valuation}(x)$. Let $F$ be a field extension of $L$ and let $\bar F_i$ ($i \in \mathrm{Fin}\,n$) be fields over the residue field of $A$, all of whose places are rational (the structure map to the residue field of the place is surjective). The combinatorial datum consists of: component charts $C_i$ of $F$ with values in $\bar F_i$ (a valuation subring of $F$ with surjective residue map onto $\bar F_i$ whose kernel is the maximal ideal, a set $\mathrm{dom}$ of places of $F/L$, a finite set of nodes in $\bar F_i$, and a specialisation map on places, subject to the axioms of `ComponentChart`), with all places of $\mathrm{dom}$ rational; annuli $\mathrm{An}_e, \mathrm{An}'_e$ ($e \in \mathrm{Fin}\,m$) with edge ends $\mathrm{src}\,e$, $\mathrm{tgt}\,e$ and nodes $x^{s}_e \in \bar F_{\mathrm{src}\,e}$, $x^{t}_e \in \bar F_{\mathrm{tgt}\,e}$, and weights $w_e \in \mathbb{N}$. The hypotheses are: $\mathrm{An}'_e$ and $\mathrm{An}_e$ have the same domain and the same modulus, that modulus is nonzero in $L$, and the product of the two parameters is the image of the modulus in $F$; the modulus of $\mathrm{An}_e$ is $u\pi^{w_e}$ for a unit $u$ of $A$; $\mathrm{An}_e$ is attached to $C_{\mathrm{src}\,e}$ at $x^{s}_e$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}\,e}$ at $x^{t}_e$ in the sense of `IsAttached`; every node of every chart is an end of some edge, and the labelling $\mathrm{Fin}\,m \oplus \mathrm{Fin}\,m \to \coprod_j \mathrm{Place}$ by edge ends is injective over the nodes; every place of $F/L$ lies either in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain; for every non-node place $Q$ of $\bar F_i$ there is $T$ in the chart integers whose residue is nonzero with $\mathrm{ord}_Q = 1$, which lies in the valuation subring of each place above $Q$ with $\mathrm{evalAt}\,T$ in the maximal ideal of $A$, and such that for each $c$ in the maximal ideal there is a unique place $P$ of the chart domain above $Q$ with $P.\mathrm{evalAt}\,T = c$; and the genus relation $g(F/L) + n = \sum_i g(\bar F_i/\kappa_A) + m + 1$, where $g$ is $\dim H^1(0)$. Both $F/L$ and each $\bar F_i/\kappa_A$ are curves in the sense of `IsCurveOver` and essentially of finite type. Given divisors $D_i$ on $F/L$ supported in $\mathrm{dom}(C_i)$, divisors $N_e$ supported in $\mathrm{dom}(\mathrm{An}_e)$ whose support places $P$ satisfy the lattice condition that $P.\mathrm{evalAt}$ of the annulus parameter lies in $A$ and equals $u\pi^{d}$ for some unit $u$ and $d \in \mathbb{N}$, slopes $\sigma_e \in \mathbb{Z}$ and nonzero scalars $a_i \in L$ such that the vertex law $\deg D_i + \sum_{\mathrm{src}\,e = i} \sigma_e + \sum_{\mathrm{tgt}\,e = i} (\mu_e - \sigma_e) = 0$ holds for every $i$, where $\mu_e$ is the total coefficient sum of $N_e$, and the edge law $A.\mathrm{valuation}(a_{\mathrm{src}\,e}) \cdot \prod_P A.\mathrm{valuation}(P.\mathrm{evalAt}\,z_e)^{N_e(P)} = A.\mathrm{valuation}(a_{\mathrm{tgt}\,e}) \cdot A.\mathrm{valuation}(\mathrm{modulus}_e)^{\mu_e - \sigma_e}$ holds for every $e$, the conclusion is that there exist divisors $D'_i$ on $F/L$, each supported in $\mathrm{dom}(C_i)$ and of degree zero, such that $\sum_i D_i + \sum_e N_e - \sum_i D'_i$ is principal, i.e. is the divisor of $\mathrm{ord}$-values of some nonzero element of $F$.
--
--   This is the moving lemma for a semistable covering of $F/L$ by component charts and annuli: a divisor which is tropically principal on the associated skeleton, the vertex and edge laws recording the slopes $\sigma_e$ and the vertex values $|a_i|$ of a tropical rational function, is linearly equivalent to a divisor supported in the charts with all chart-degrees zero. It is the converse, up to the bounded part, of the slope law, and is used in the description of chart-supported representatives for invariants of the rational Tate module of a semistable model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_add_sum_sub_sum_mem_principal_of_degree_add_sum_eq_zero_of_valuation_mul_prod_eq_of_lattice_of_semistableCovering_of_discFibres_of_rankOne.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open scoped TensorProduct

theorem
    AlgebraicCurve.exists_add_sum_sub_sum_mem_principal_of_degree_add_sum_eq_zero_of_valuation_mul_prod_eq_of_lattice_of_semistableCovering_of_discFibres_of_rankOne
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
    (Di : Fin n → Divisor L F) (hdom : ∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom)
    (N : Fin m → Divisor L F) (hNdom : ∀ e, ∀ P ∈ (N e).support, P ∈ (An e).dom)
    (hNlat : ∀ e, ∀ P ∈ (N e).support, ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
      (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d)
    (σ : Fin m → ℤ) (a : Fin n → L) (ha : ∀ i, a i ≠ 0)
    (hV : ∀ i : Fin n, Divisor.degree (Di i) + (∑ e, if src e = i then σ e else 0) +
        (∑ e, if tgt e = i then ((N e).sum fun _ k => k) - σ e else 0) = 0)
    (hE : ∀ e : Fin m, A.valuation (a (src e)) * ((N e).prod fun P k => A.valuation (P.evalAt (An e).param) ^ k) =
        A.valuation (a (tgt e)) * A.valuation ((An e).modulus : L) ^ (((N e).sum fun _ k => k) - σ e))
    :
    ∃ Di' : Fin n → Divisor L F,
      (∀ i, ∀ P ∈ (Di' i).support, P ∈ (C i).dom) ∧ (∀ i, Divisor.degree (Di' i) = 0) ∧
      (∑ i, Di i) + (∑ e, N e) - (∑ i, Di' i) ∈ Divisor.principal (K := L) (F := F) := by sorry
