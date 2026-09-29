-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_residue_evalAt_eq_evalAt_residue_of_ord_residue_eq_zero_of_regularProlongation_modulus_div_param
-- name    : AlgebraicCurve.Annulus.residue_evalAt_eq_evalAt_residue_of_ord_residue_eq_zero_of_regularProlongation_modulus_div_param
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/b18d787c-08fb-5fac-ac09-e4ef327ae1f7
-- title:
--   Unit reduction on an annulus read at the second end
-- statement:
--   Let $L$ be an algebraically closed field, $A\subseteq L$ a valuation subring with residue field $\kappa=$ `IsLocalRing.ResidueField A`, $F$ a field extension of $L$ satisfying `HasPrincipalDivisors L F` (every nonzero $f\in F$ has a finitely supported divisor of degree $0$ whose coefficient at each place $v$ of $F/L$ is $\operatorname{ord}_v f$), and $Fb$ a field extension of $\kappa$. Let `An` be an annulus of $F/L$ over $A$: a set `An.dom` of places of $F/L$, a parameter $z=$ `An.param` $\in F$ and a modulus $\varpi=$ `An.modulus` in the maximal ideal of $A$, such that each $P\in$ `An.dom` is rational with $z$ integral at $P$, $z(P)$ a nonzero element of the maximal ideal of $A$ dividing $\varpi$, that every admissible value is attained by a unique place of `An.dom`, that $\operatorname{ord}_P(z-z(P))=1$, and that the unit principle holds for functions without zeros or poles on `An.dom`. Assume $\varpi\neq 0$ in $L$. Let `Rb` be a regular prolongation of $A$ to $F$ with residue field $Fb$, i.e. a valuation subring `Rb.integers` of $F$ meeting $L$ exactly in $A$, equipped with a surjective residue homomorphism to $Fb$ whose kernel is the maximal ideal, compatible with the residue map of $A$, and such that every nonzero element of $F$ becomes, after scaling by an element of $L$, integral with nonzero residue. Let $xb$ be a place of $Fb/\kappa$. Assume: the reflected parameter $z'=\varpi z^{-1}$ (formed in $F$) lies in `Rb.integers`; $\operatorname{ord}_{xb}$ of its residue equals $1$; the end-slope law, namely that for every $f\in$ `Rb.integers` with nonzero residue $\bar f$ and with $\operatorname{ord}_P f=0$ for all $P\in$ `An.dom`, the element $f(P)\,z'(P)^{-\operatorname{ord}_{xb}\bar f}$ lies in $A$ and is a unit of $A$ for every $P\in$ `An.dom`; and that $xb$ is rational, i.e. $\kappa\to$ `xb.ResidueField` is surjective. Finally let $u\in$ `Rb.integers` have nonzero residue $\bar u$ with $\operatorname{ord}_{xb}\bar u=0$, and satisfy $\operatorname{ord}_P u=0$ for all $P\in$ `An.dom`. Then for every $P\in$ `An.dom` the value $P.\mathrm{evalAt}\,u$ lies in $A$, is a unit of $A$, and its residue class in $\kappa$ equals $xb.\mathrm{evalAt}\,\bar u$.
--
--   This is the end-reading statement for an annulus at its second end, where the end is presented through the reflected parameter $\varpi/z$ rather than through $z$: a function integral at the prolongation whose residue is regular and nonvanishing at the chosen place $xb$ has constant unit reduction along the whole annulus, and that constant reduction is the value of the residue at $xb$. It feeds the computation of orders and of the reduced values of $\mathrm{evalAt}$ twisted by powers of the parameter in [`AlgebraicCurve.Annulus.ord_residue_eq_neg_and_evalAt_residue_mul_zpow_eq_of_forall_ord_eq_zero_of_rankOne`](thm.html#AlgebraicCurve.Annulus.ord_residue_eq_neg_and_evalAt_residue_mul_zpow_eq_of_forall_ord_eq_zero_of_rankOne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_residue_evalAt_eq_evalAt_residue_of_ord_residue_eq_zero_of_regularProlongation_modulus_div_param.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Annulus.residue_evalAt_eq_evalAt_residue_of_ord_residue_eq_zero_of_regularProlongation_modulus_div_param
    {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (An : Annulus A F) (hmod0 : (An.modulus : L) ≠ 0)
    (Rb : RegularProlongation A F Fb) (xb : Place (IsLocalRing.ResidueField A) Fb)
    (hzb : algebraMap L F (An.modulus : L) * An.param⁻¹ ∈ Rb.integers)
    (hxb : xb.ord (Rb.residue ⟨algebraMap L F (An.modulus : L) * An.param⁻¹, hzb⟩) = 1)
    (hslope_b : ∀ (f : F) (hf : f ∈ Rb.integers), Rb.residue ⟨f, hf⟩ ≠ 0 →
      (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
        ∃ h : P.evalAt f * (P.evalAt (algebraMap L F (An.modulus : L) * An.param⁻¹)) ^
          (-(xb.ord (Rb.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A))
    (hxb_rat : xb.IsRational)
    (u : F) (hu : u ∈ Rb.integers) (hres : Rb.residue ⟨u, hu⟩ ≠ 0)
    (hord : xb.ord (Rb.residue ⟨u, hu⟩) = 0)
    (hzero : ∀ P ∈ An.dom, P.ord u = 0) :
    ∀ P ∈ An.dom, ∃ h : P.evalAt u ∈ A, IsUnit (⟨_, h⟩ : A) ∧
      IsLocalRing.residue A ⟨P.evalAt u, h⟩ = xb.evalAt (Rb.residue ⟨u, hu⟩) := by sorry
