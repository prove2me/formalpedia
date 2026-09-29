-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_IsAttached_of_param_eq_of_forall_mem_dom_iff
-- name    : AlgebraicCurve.Annulus.IsAttached.of_param_eq_of_forall_mem_dom_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/1631c42f-0d9c-5dd9-9837-4a45bac8e252
-- title:
--   Attachment passes to upper subannuli with the same parameter
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring, $F$ a field extension of $L$ for which `HasPrincipalDivisors L F` holds (every $f \in F^{\times}$ is the divisor of its orders at the places of $F/L$, and that divisor has degree $0$), and $\bar F$ a field extension of the residue field of $A$. Let $\mathcal A_0$ be an annulus for $A$ in $F$ (a set of places of $F/L$ together with a parameter $z = \mathcal A_0.\mathrm{param} \in F$ and a modulus in the maximal ideal of $A$, subject to the axioms of `Annulus`), $C$ a component chart of $F$ over $A$ with values in $\bar F$, and $x$ a place of $\bar F$ over the residue field of $A$. Assume $\mathcal A_0$ is attached to $C$ at $x$, that is: $x$ is one of the nodes of $C$, the parameter $z$ lies in the valuation subring $C.\mathrm{integers}$ and its $C$-reduction has order $1$ at $x$, and for every $f \in C.\mathrm{integers}$ whose $C$-reduction is nonzero and which has order $0$ at every place of $\mathcal A_0.\mathrm{dom}$, one has at each $P \in \mathcal A_0.\mathrm{dom}$ that $f(P)\,z(P)^{-\operatorname{ord}_x \bar f}$ lies in $A$ and is a unit there (values $f(P)$ being taken by `Place.evalAt`, i.e. via the inverse of $L \to$ residue field of $P$). Let $\mathcal B$ be a further annulus with $\mathcal B.\mathrm{param} = z$, and let $b \in L$ be such that a place $P$ lies in $\mathcal B.\mathrm{dom}$ exactly when $P \in \mathcal A_0.\mathrm{dom}$ and $v(b) < v(z(P))$, where $v$ is the valuation of $L$ attached to $A$. Then $\mathcal B$ is attached to $C$ at $x$ in the same sense.
--
--   This is the transfer of the attachment relation (node, uniformising reduction of the parameter, and the unit law relating the value of a $C$-unit to a power of the parameter) from an annulus to the subannulus cut out by an inequality on the parameter, the two annuli sharing their parameter. It is used in the construction of circle charts and bands of width one in a semistable covering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_IsAttached_of_param_eq_of_forall_mem_dom_iff.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Annulus.IsAttached.of_param_eq_of_forall_mem_dom_iff
    {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField ↥A) Fb]
    (An₀ : Annulus A F) (C : ComponentChart A F Fb) (x : Place (IsLocalRing.ResidueField ↥A) Fb)
    (hatt : An₀.IsAttached C x)
    (B : Annulus A F) (hparam : B.param = An₀.param)
    (b : L) (hdom : ∀ P, P ∈ B.dom ↔ P ∈ An₀.dom ∧ A.valuation b < A.valuation (P.evalAt An₀.param)) :
    B.IsAttached C x := by sorry
