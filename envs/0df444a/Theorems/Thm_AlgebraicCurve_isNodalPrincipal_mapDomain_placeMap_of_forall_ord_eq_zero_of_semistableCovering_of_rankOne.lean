-- Prove2me | Theorems.Thm_AlgebraicCurve_isNodalPrincipal_mapDomain_placeMap_of_forall_ord_eq_zero_of_semistableCovering_of_rankOne
-- name    : AlgebraicCurve.isNodalPrincipal_mapDomain_placeMap_of_forall_ord_eq_zero_of_semistableCovering_of_rankOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/ffe767c0-291a-51d3-b1fc-4ee24556407c
-- title:
--   Chartwise reduction of a principal divisor is nodal principal
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring, $\pi \in A$ a nonzero element of the maximal ideal, and assume $A$ has rank one in the form: for every $x \in L^{\times}$ and every $y$ in the maximal ideal of $A$ there is $n \in \mathbb{N}$ with $v_A(y^n) \le v_A(x)$. Let $F$ be a field extension of $L$ in which every nonzero element has a divisor of degree zero recording its orders at all places of $F/L$, and let $\bar F_0, \dots, \bar F_{n-1}$ be field extensions of $\kappa =$ the residue field of $A$ with the same principal-divisor property and with all places of $\bar F_i/\kappa$ rational. For each $i$ let $C_i$ be a component chart for $(A, F, \bar F_i)$ — a valuation subring of $F$ whose elements of $L$ are exactly $A$, a surjective residue map onto $\bar F_i$ with kernel the maximal ideal and compatible with the residue map of $A$, a set $\mathrm{dom}$ of places of $F/L$, a finite set $\mathrm{nodes}$ of places of $\bar F_i/\kappa$, and a reduction map $\mathrm{placeMap}$ on places, subject to the axioms of `ComponentChart` (non-nodal image, pointwise compatibility of evaluation with reduction, and the push-forward law for divisors of chart integers) — and assume every place in $C_i.\mathrm{dom}$ is rational. Let $\mathrm{An}_e, \mathrm{An}'_e$ ($e \in \mathrm{Fin}\,m$) be annuli in $F$ over $A$, with $\mathrm{src}, \mathrm{tgt} : \mathrm{Fin}\,m \to \mathrm{Fin}\,n$, places $x_s(e)$ of $\bar F_{\mathrm{src}(e)}$ and $x_t(e)$ of $\bar F_{\mathrm{tgt}(e)}$, and widths $w_e \in \mathbb{N}$, such that for every $e$: $\mathrm{An}'_e$ has the same domain and the same modulus as $\mathrm{An}_e$, that modulus is nonzero in $L$ and equals the product of the two parameters, and the modulus is $u\pi^{w_e}$ for some unit $u$ of $A$; moreover $\mathrm{An}_e$ is attached to $C_{\mathrm{src}(e)}$ at $x_s(e)$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}(e)}$ at $x_t(e)$ (the node lies in the chart's node set, the annulus parameter lies in the chart integers with reduction of order $1$ at the node, and for every chart integer $f$ with nonzero reduction and no zeros or poles on the annulus, $P(f) \cdot P(\text{param})^{-\mathrm{ord}_x(\bar f)}$ is a unit of $A$ at each place $P$ of the annulus). Assume each node $x$ of each $C_i$ is an end of at least one annulus, and that the two end-assignments $e \mapsto (\mathrm{src}(e), x_s(e))$ and $e \mapsto (\mathrm{tgt}(e), x_t(e))$, combined into a map from $\mathrm{Fin}\,m \oplus \mathrm{Fin}\,m$, take the value $(i,x)$ for at most one argument. Finally let $f \in F$ be nonzero, and let $D_i$ be divisors of $F/L$ supported in $C_i.\mathrm{dom}$, with $D_i(P) = \mathrm{ord}_P(f)$ for $P \in C_i.\mathrm{dom}$, each of degree zero, and suppose $\mathrm{ord}_P(f) = 0$ for every place $P$ in every annulus domain. Then the family $i \mapsto (\mathrm{placeMap}_{C_i})_{*} D_i$ is nodal principal: there exist nonzero $g_i \in \bar F_i$ and units $a_e \in \kappa^{\times}$ such that $((\mathrm{placeMap}_{C_i})_{*} D_i)(Q) = \mathrm{ord}_Q(g_i)$ for every place $Q$ of $\bar F_i/\kappa$, and for every $e$ the element $g_{\mathrm{src}(e)}$ lies in the valuation ring of $x_s(e)$ with residue the image of $a_e$, and likewise $g_{\mathrm{tgt}(e)}$ at $x_t(e)$.
--
--   This is the well-definedness of the chartwise reduction map from degree-zero divisor classes supported in the chart domains of a semistable covering to the Picard group of the nodal special fibre: principal divisors reduce to nodal principal data. It is used in the bound on the torsion of the group of tropical position zero for a semistable model over a rank-one valuation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_isNodalPrincipal_mapDomain_placeMap_of_forall_ord_eq_zero_of_semistableCovering_of_rankOne.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_NodalPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.isNodalPrincipal_mapDomain_placeMap_of_forall_ord_eq_zero_of_semistableCovering_of_rankOne
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type*) [Field F] [Algebra L F] [HasPrincipalDivisors L F]
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
    (f : F) (hf : f ≠ 0)
    (Di : Fin n → Divisor L F) (hdom : ∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom)
    (hDi : ∀ i, ∀ P ∈ (C i).dom, Di i P = P.ord f)
    (hdeg : ∀ i, Divisor.degree (Di i) = 0)
    (hN0 : ∀ e, ∀ P ∈ (An e).dom, P.ord f = 0) :
    NodalData.IsNodalPrincipal (K := IsLocalRing.ResidueField A) (Fbar := Fbar) src tgt xs xt
      (fun i => Finsupp.mapDomain (C i).placeMap (Di i)) := by sorry
