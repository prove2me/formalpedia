-- Prove2me | Theorems.Thm_AlgebraicCurve_mapDomain_placeMap_mem_principal_of_forall_support_subset_dom_of_degree_eq_zero
-- name    : AlgebraicCurve.mapDomain_placeMap_mem_principal_of_forall_support_subset_dom_of_degree_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/2b530064-5abc-5208-bb9c-8c5b7fed5804
-- title:
--   Chart components of a principal divisor push forward to principal divisors
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring, $\pi$ a nonzero element of the maximal ideal of $A$, and write $\kappa$ for the residue field of $A$; let $F$ be a field extension of $L$. Fix $n, m \in \mathbb{N}$ and, for each $i < n$, a field $\overline{F}_i$ over $\kappa$ in which every nonzero element has a (finitely supported) divisor of degree zero recording its order at all places, all places of $\overline{F}_i$ over $\kappa$ being rational (the structure map to the residue field of the place is surjective), together with a component chart $C_i$ of $F$ over $A$ with residue field $\overline{F}_i$, all places in $(C_i).\mathrm{dom}$ being rational over $L$. For each $e < m$ let $\mathrm{An}_e, \mathrm{An}'_e$ be annuli of $F$ over $A$ with equal domains and equal moduli, the modulus nonzero in $L$, the product of the two parameters equal to the image of the modulus in $F$, and the modulus a unit of $A$ times $\pi^{w_e}$ for some $w_e \in \mathbb{N}$; let $\mathrm{src}(e), \mathrm{tgt}(e) < n$ and places $x^s_e$ of $\overline{F}_{\mathrm{src}(e)}$, $x^t_e$ of $\overline{F}_{\mathrm{tgt}(e)}$ be such that $\mathrm{An}_e$ is attached to $C_{\mathrm{src}(e)}$ at $x^s_e$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}(e)}$ at $x^t_e$ (each attachment asserting that the place is a node of the chart, that the annulus parameter lies in the chart's integers with residue of order $1$ at that place, and the slope condition on units of the annulus). Assume further that every node $x$ of every $C_i$ is an endpoint $(\mathrm{src}(e), x^s_e)$ or $(\mathrm{tgt}(e), x^t_e)$ of some annulus and that such an endpoint, indexed by $\mathrm{Fin}\,m \oplus \mathrm{Fin}\,m$, is unique; and that every place $P$ of $F$ over $L$ lies either in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain. Finally let $f \in F$ be nonzero, $D$ the divisor with $D(P) = \mathrm{ord}_P(f)$ for all $P$, and $D = \sum_i D_i$ a decomposition with $\operatorname{supp}(D_i) \subseteq (C_i).\mathrm{dom}$ and $\deg D_i = 0$. The conclusion is that for every $i$ the push-forward of $D_i$ along $(C_i).\mathrm{placeMap}$ lies in the group of principal divisors of $\overline{F}_i$ over $\kappa$, i.e. equals $\mathrm{ord}(g)$ for some nonzero $g \in \overline{F}_i$.
--
--   This is the specialisation step for principal divisors on a semistable covering of $F$ by component charts glued along annuli: the annulus slopes of $f$ form a harmonic gradient on the associated weighted multigraph, hence vanish, so each chart component of the divisor of $f$ descends to a principal divisor on the corresponding residue curve. It is used in the construction of the reduction map on the rational Tate module attached to a semistable model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_mapDomain_placeMap_mem_principal_of_forall_support_subset_dom_of_degree_eq_zero.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.mapDomain_placeMap_mem_principal_of_forall_support_subset_dom_of_degree_eq_zero
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
    (f : F) (hf : f ≠ 0) (D : Divisor L F) (hDf : ∀ P, D P = P.ord f)
    (Di : Fin n → Divisor L F) (hsum : D = ∑ i, Di i)
    (hdom : ∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) (hdeg : ∀ i, Divisor.degree (Di i) = 0)
    :
    ∀ i, Finsupp.mapDomain (C i).placeMap (Di i) ∈
      Divisor.principal (K := IsLocalRing.ResidueField A) (F := Fbar i) := by sorry
