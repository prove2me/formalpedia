-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableCovering_exists_linearIndependent_pi_residue_smul_of_mem_riemannRochSpace_of_rankOne
-- name    : AlgebraicCurve.SemistableCovering.exists_linearIndependent_pi_residue_smul_of_mem_riemannRochSpace_of_rankOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/64b52bba-ee30-5951-b171-af469d2e6e55
-- title:
--   Weighted reductions of a Riemann–Roch space are independent
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring and $\pi \in A$ a nonzero element of the maximal ideal, and assume $A$ has rank one in the sense that for every $x \in L^{\times}$ and every $y$ in the maximal ideal some power $y^{n}$ has valuation at most that of $x$; write $\kappa$ for the residue field of $A$. Let $F$ be a field extension of $L$ which is a curve over $L$ (principal divisors exist, all residue fields of places are finite over $L$, and $\Omega_{F/L}$ is free of rank one) and essentially of finite type over $L$. Let $n, m \in \mathbb{N}$, let $\bar{F}_i$ ($i \in \mathrm{Fin}\,n$) be fields over $\kappa$ that are curves over $\kappa$ and essentially of finite type over $\kappa$, all of whose places are rational (the structure map to each residue field is surjective), and for each $i$ let $C_i$ be a component chart for $A$, $F$, $\bar{F}_i$: a valuation subring $(C_i).\mathrm{integers}$ of $F$ whose intersection with $L$ is $A$, a surjective reduction homomorphism onto $\bar{F}_i$ with kernel the maximal ideal, a set $(C_i).\mathrm{dom}$ of places of $F/L$, a finite set $(C_i).\mathrm{nodes}$ of places of $\bar{F}_i/\kappa$ and a map $(C_i).\mathrm{placeMap}$ from places of $F/L$ to places of $\bar{F}_i/\kappa$, subject to the axioms of `ComponentChart` (compatibility of reduction with $A$, avoidance of nodes, the pointwise evaluation axiom and the divisor-pushforward axiom); assume every place in $(C_i).\mathrm{dom}$ is rational over $L$. Let $\mathrm{An}_e, \mathrm{An}'_e$ ($e \in \mathrm{Fin}\,m$) be annuli for $A$, $F$ (each a set of places, a parameter in $F$ and a modulus in the maximal ideal of $A$, with the axioms of `Annulus`), let $\mathrm{src}, \mathrm{tgt} : \mathrm{Fin}\,m \to \mathrm{Fin}\,n$, let $x^{s}_e$ be a place of $\bar{F}_{\mathrm{src}(e)}/\kappa$ and $x^{t}_e$ a place of $\bar{F}_{\mathrm{tgt}(e)}/\kappa$, and let $w : \mathrm{Fin}\,m \to \mathbb{N}$. Assume: for each $e$ the two annuli $\mathrm{An}_e$, $\mathrm{An}'_e$ have the same domain and the same modulus, that modulus is nonzero in $L$ and the product of the two parameters is the image of the modulus; the modulus of $\mathrm{An}_e$ is a unit times $\pi^{w(e)}$; $\mathrm{An}_e$ is attached to $C_{\mathrm{src}(e)}$ at $x^{s}_e$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}(e)}$ at $x^{t}_e$ (the attachment point is a node, the parameter lies in the chart's integers with reduction of order $1$ there, together with the unit condition in `IsAttached`); every node of every chart occurs as such an endpoint, and the $2m$ endpoints, viewed as pairs (index, place), are pairwise distinct at each node; every place of $F/L$ lies either in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain; for each $i$ and each non-node place $Q$ of $\bar{F}_i/\kappa$ there is $T$ in $(C_i).\mathrm{integers}$ with nonzero reduction of order $1$ at $Q$, such that $T$ lies in the valuation ring of every $P \in (C_i).\mathrm{dom}$ with $(C_i).\mathrm{placeMap}(P) = Q$ and $P$-value of $T$ lies in the maximal ideal of $A$, and such that every $c$ in the maximal ideal of $A$ is the $P$-value of $T$ for exactly one such $P$; and the genus identity $g(F/L) + n = \sum_i g(\bar{F}_i/\kappa) + m + 1$, the genus being the $\kappa$- resp. $L$-dimension of $H^{1}$ of the zero divisor. Then for every divisor $D$ of $F/L$ and every $\varphi : \mathrm{Fin}\,n \to \mathbb{Z}$ there are elements $s_j \in F$, indexed by $j \in \mathrm{Fin}(\dim_L \mathcal{L}(D))$, all lying in the Riemann–Roch space $\mathcal{L}(D)$, such that $\pi^{-\varphi(i)} s_j$ lies in $(C_i).\mathrm{integers}$ for all $i$ and $j$, and the resulting family of tuples $j \mapsto \bigl((C_i).\mathrm{residue}(\pi^{-\varphi(i)} s_j)\bigr)_i$ in $\prod_i \bar{F}_i$ is linearly independent over $\kappa$.
--
--   This is the statement that reduction to the components of a semistable covering does not lower the dimension of a linear system, in the form of Deuring's theory of constant reduction of function fields, extended to all charts of the covering simultaneously and with arbitrary integral weights $\varphi$ attached to the components. It is used in the construction of functions with prescribed reduction behaviour on such coverings, in particular by [`AlgebraicCurve.SemistableCovering.exists_forall_residue_smul_eq_of_forall_ord_ge_of_forall_evalAt_mul_eq_of_width_one`](thm.html#AlgebraicCurve.SemistableCovering.exists_forall_residue_smul_eq_of_forall_ord_ge_of_forall_evalAt_mul_eq_of_width_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableCovering_exists_linearIndependent_pi_residue_smul_of_mem_riemannRochSpace_of_rankOne.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.SemistableCovering.exists_linearIndependent_pi_residue_smul_of_mem_riemannRochSpace_of_rankOne
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
    (D : Divisor L F) (φ : Fin n → ℤ)
    :
    ∃ s : Fin (Module.finrank L (riemannRochSpace D)) → F,
      ∃ hs : ∀ j i, ((((π : A) : L) ^ (φ i))⁻¹ • s j) ∈ (C i).integers,
        (∀ j, s j ∈ riemannRochSpace D) ∧
        LinearIndependent (IsLocalRing.ResidueField A)
          (fun j => fun i => (C i).residue ⟨(((π : A) : L) ^ (φ i))⁻¹ • s j, hs j i⟩) := by sorry
