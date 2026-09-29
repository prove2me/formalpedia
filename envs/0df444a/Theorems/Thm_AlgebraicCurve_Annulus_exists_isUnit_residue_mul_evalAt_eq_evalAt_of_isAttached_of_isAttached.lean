-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_exists_isUnit_residue_mul_evalAt_eq_evalAt_of_isAttached_of_isAttached
-- name    : AlgebraicCurve.Annulus.exists_isUnit_residue_mul_evalAt_eq_evalAt_of_isAttached_of_isAttached
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/90147155-3cd9-5b9e-af5d-6626126552e0
-- title:
--   Two-end residue law for a doubly attached annulus
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring satisfying the rank-one condition `hrk`: for every $x \neq 0$ in $L$ and every $y$ in the maximal ideal of $A$ there is $n \in \mathbb{N}$ with $A.\mathrm{valuation}(y^n) \le A.\mathrm{valuation}(x)$. Let $F$ be a field extension of $L$ in which every nonzero element has a degree-zero divisor realising its orders at all places (`HasPrincipalDivisors`), and let $F_a, F_b$ be extensions of the residue field $k = A/\mathfrak{m}_A$ all of whose places over $k$ are rational, i.e. $k$ surjects onto each residue field. Let $\mathrm{An}, \mathrm{An}'$ be annuli for $A$ in $F$ with the same domain of places, with $\mathrm{An}'.\mathrm{param} \cdot \mathrm{An}.\mathrm{param}$ equal to the image of the modulus $q = \mathrm{An}.\mathrm{modulus}$, and with $q \neq 0$ in $L$. Let $C_a$ be a component chart for $A, F, F_a$ and $x_a$ a place of $F_a$ over $k$ with $\mathrm{An}.\mathrm{IsAttached}\, C_a\, x_a$, that is: $x_a$ lies in the nodes of $C_a$, the parameter $z = \mathrm{An}.\mathrm{param}$ lies in $C_a.\mathrm{integers}$ with $\mathrm{ord}_{x_a}$ of its residue equal to $1$, and for every $C_a$-integral $f$ with nonzero residue whose order vanishes at all places of the annulus and every such place $P$, the element $P.\mathrm{evalAt}(f) \cdot P.\mathrm{evalAt}(z)^{-\mathrm{ord}_{x_a}(\bar f)}$ lies in $A$ and is a unit there; let $C_b, x_b$ satisfy the same for $\mathrm{An}'$. Let $h \neq 0$ in $F$ be $C_a$-integral with nonzero residue $\bar h_a = C_a.\mathrm{residue}(h)$, let $c' \neq 0$ in $L$ be such that $c'^{-1}h$ is $C_b$-integral with nonzero residue $\bar h_b$, and let $D$ be a divisor of $F/L$ supported in $\mathrm{An}.\mathrm{dom}$ with $D(P) = P.\mathrm{ord}(h)$ for every $P \in \mathrm{An}.\mathrm{dom}$. Then the element $$u \;=\; c'^{-1}\, q^{\,\mathrm{ord}_{x_a}(\bar h_a) - \sum_P D(P)} \prod_P \bigl(-P.\mathrm{evalAt}(z)\bigr)^{D(P)}$$ of $L$ (sum and product over the support of $D$) lies in $A$, is a unit of $A$, and its residue in $k$ satisfies $$\mathrm{residue}(u) \cdot x_a.\mathrm{evalAt}\bigl(\bar h_a \cdot C_a.\mathrm{residue}(z)^{-\mathrm{ord}_{x_a}(\bar h_a)}\bigr) \;=\; x_b.\mathrm{evalAt}\bigl(\bar h_b \cdot C_b.\mathrm{residue}(\mathrm{An}'.\mathrm{param})^{-\mathrm{ord}_{x_b}(\bar h_b)}\bigr),$$ where the residues of the parameters are taken with respect to the integrality witnesses contained in the two attachment hypotheses.
--
--   This is the residue-level form of the two-end law for a function on an annulus in the sense of Bosch–Lütkebohmert's analysis of functions on formal annuli: the leading coefficients of $h$ at the two nodes to which the annulus is attached differ by the residue of an explicit unit of $A$ built from the modulus and the annulus zeros and poles of $h$. It refines the zero-free case [`AlgebraicCurve.Annulus.ord_residue_eq_neg_and_evalAt_residue_mul_zpow_eq_of_forall_ord_eq_zero_of_rankOne`](thm.html#AlgebraicCurve.Annulus.ord_residue_eq_neg_and_evalAt_residue_mul_zpow_eq_of_forall_ord_eq_zero_of_rankOne), which it cites, and is used in the treatment of nodal principal divisors and of Kummer classes attached to a semistable covering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_exists_isUnit_residue_mul_evalAt_eq_evalAt_of_isAttached_of_isAttached.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Annulus.exists_isUnit_residue_mul_evalAt_eq_evalAt_of_isAttached_of_isAttached
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    {Fa : Type*} [Field Fa] [Algebra (IsLocalRing.ResidueField A) Fa]
    {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (hratA : ∀ x : Place (IsLocalRing.ResidueField A) Fa, x.IsRational)
    (hratB : ∀ x : Place (IsLocalRing.ResidueField A) Fb, x.IsRational)
    (An An' : Annulus A F) (hdom : An'.dom = An.dom)
    (hparam : An'.param * An.param = algebraMap L F (An.modulus : L)) (hmod0 : (An.modulus : L) ≠ 0)
    (Ca : ComponentChart A F Fa) (xa : Place (IsLocalRing.ResidueField A) Fa) (hatt : An.IsAttached Ca xa)
    (Cb : ComponentChart A F Fb) (xb : Place (IsLocalRing.ResidueField A) Fb) (hatt' : An'.IsAttached Cb xb)
    (h : F) (hh0 : h ≠ 0) (hha : h ∈ Ca.integers) (hresa : Ca.residue ⟨h, hha⟩ ≠ 0)
    (c' : L) (hc'0 : c' ≠ 0)
    (hhb : (algebraMap L F c')⁻¹ * h ∈ Cb.integers) (hresb : Cb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩ ≠ 0)
    (D : Divisor L F) (hDsupp : ∀ P ∈ D.support, P ∈ An.dom) (hD : ∀ P ∈ An.dom, D P = P.ord h)
    :
    ∃ hu : c'⁻¹ * (An.modulus : L) ^ (xa.ord (Ca.residue ⟨h, hha⟩) - (D.sum fun _ k => k)) *
        (D.prod fun P k => (-(P.evalAt An.param)) ^ k) ∈ A,
      IsUnit (⟨_, hu⟩ : A) ∧
      IsLocalRing.residue A ⟨_, hu⟩ *
          xa.evalAt (Ca.residue ⟨h, hha⟩ * (Ca.residue ⟨An.param, hatt.2.choose⟩) ^ (-(xa.ord (Ca.residue ⟨h, hha⟩)))) =
        xb.evalAt (Cb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩ *
          (Cb.residue ⟨An'.param, hatt'.2.choose⟩) ^ (-(xb.ord (Cb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩)))) := by sorry
