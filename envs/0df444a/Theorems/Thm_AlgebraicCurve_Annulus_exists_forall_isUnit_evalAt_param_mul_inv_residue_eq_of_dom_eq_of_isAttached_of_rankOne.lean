-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_exists_forall_isUnit_evalAt_param_mul_inv_residue_eq_of_dom_eq_of_isAttached_of_rankOne
-- name    : AlgebraicCurve.Annulus.exists_forall_isUnit_evalAt_param_mul_inv_residue_eq_of_dom_eq_of_isAttached_of_rankOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/03d038ce-cae8-5469-b21a-a5652273e395
-- title:
--   Two annuli with the same domain: parameter ratio is a unit of constant residue
-- statement:
--   Let $L$ be an algebraically closed field and $A$ a valuation subring of $L$ which is of rank one in the following sense: for every $x \in L$, $x \neq 0$, and every $y$ in the maximal ideal of $A$ there is $n \in \mathbb{N}$ with $v_A(y^n) \le v_A(x)$. Let $F$ be a field extension of $L$ that is a curve over $L$ (principal divisors of degree zero exist for all nonzero elements, every place of $F/L$ has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank one over $F$) and essentially of finite type over $L$, and let $\bar F$ be a field extension of the residue field $\kappa$ of $A$. Let $\mathrm{An}_1, \mathrm{An}_2$ be annuli for $A$ in $F$, each consisting of a set of places of $F/L$, a parameter in $F$ and a modulus in the maximal ideal of $A$ subject to the axioms of `Annulus` (the parameter is integral with nonzero value in the maximal ideal at each place of the domain, the modulus is divisible by that value, each admissible value is attained at a unique place of the domain, the parameter minus its value has order one, and the unit principle holds); write $z_1, z_2$ for their parameters and assume the two domains coincide, $D := \mathrm{An}_1.\mathrm{dom}$. For a place $P$ and $f \in F$, $f(P) :=$ `P.evalAt f` denotes the element of $L$ mapping to the reduction of $f$ at $P$ when $f$ is $P$-integral, and $0$ otherwise. Let $C$ be a component chart for $(A, F, \bar F)$, with Gauss ring `C.integers`, reduction map `C.residue` to $\bar F$, domain and finite set of nodes, and let $x$ be a place of $\bar F$ over $\kappa$ which is rational, i.e. $\kappa$ surjects onto its residue field. Assume $\mathrm{An}_1$ is attached to $C$ at $x$: $x$ is a node of $C$, the parameter $z_1$ lies in `C.integers` and its reduction has order $1$ at $x$, and for every $f \in$ `C.integers` with nonzero reduction and order $0$ at all places of $D$, the element $f(P) \, z_1(P)^{-\mathrm{ord}_x(\bar f)}$ lies in $A$ and is a unit there, for all $P \in D$. Assume finally that $z_2$ lies in `C.integers` with nonzero reduction. Then there is a nonzero $r \in \kappa$ such that for every $P \in D$ the ratio $z_2(P) \, z_1(P)^{-1}$ lies in $A$, is a unit of $A$, and has residue $r$.
--
--   This compares two annulus structures carried by one and the same set of places when one of them is read off from an attached end of a component chart: their parameters agree, on the whole domain, up to a unit of $A$ with one fixed residue. It is used in the part of the semistable-covering analysis that transports an annulus along an isomorphism of function fields and compares parameter ratios at pairs of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_exists_forall_isUnit_evalAt_param_mul_inv_residue_eq_of_dom_eq_of_isAttached_of_rankOne.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem
    AlgebraicCurve.Annulus.exists_forall_isUnit_evalAt_param_mul_inv_residue_eq_of_dom_eq_of_isAttached_of_rankOne
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type) [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    {Fbar : Type} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (An₁ An₂ : Annulus A F) (hdom : An₂.dom = An₁.dom)
    (C : ComponentChart A F Fbar) (x : Place (IsLocalRing.ResidueField A) Fbar) (hx : x.IsRational)
    (hatt : An₁.IsAttached C x)
    (hz₂ : ∃ h : An₂.param ∈ C.integers, C.residue ⟨An₂.param, h⟩ ≠ 0) :
    ∃ r : IsLocalRing.ResidueField A, r ≠ 0 ∧
      ∀ P ∈ An₁.dom, ∃ h : P.evalAt An₂.param * (P.evalAt An₁.param)⁻¹ ∈ A,
        IsUnit (⟨_, h⟩ : A) ∧ IsLocalRing.residue A ⟨_, h⟩ = r := by sorry
