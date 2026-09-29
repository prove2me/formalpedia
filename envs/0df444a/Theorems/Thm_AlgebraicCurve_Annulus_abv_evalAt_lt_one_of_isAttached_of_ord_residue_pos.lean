-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_abv_evalAt_lt_one_of_isAttached_of_ord_residue_pos
-- name    : AlgebraicCurve.Annulus.abv_evalAt_lt_one_of_isAttached_of_ord_residue_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/8ca6b328-07b4-52a3-8f9a-c6d99f8af748
-- title:
--   Chart functions of positive order at a node are small on the attached annulus
-- statement:
--   Let $L$ be a field, $A$ a valuation subring of $L$, $F$ a field extension of $L$, and $\bar F$ a field extension of the residue field of $A$. Let $\mu$ be a real absolute value on $L$ whose closed unit disc is exactly $A$, that is, $a \in A \iff \mu(a) \le 1$. Let `An` be an annulus for $A$ in $F$ (with its set of places `An.dom`, its parameter `An.param` and its modulus in the maximal ideal of $A$), `C` a component chart for $A$, $F$, $\bar F$ (with valuation subring `C.integers`, reduction map `C.residue` onto $\bar F$, set of places `C.dom`, finite set of nodes `C.nodes` and place map), and $x$ a place of $\bar F$ over the residue field of $A$. Assume `An.IsAttached C x`, i.e. $x$ is a node of `C`, the parameter lies in `C.integers` and its reduction has $\operatorname{ord}_x$ equal to $1$, and the slope law holds: for every $g \in$ `C.integers` with nonzero reduction and $\operatorname{ord}_P g = 0$ at all $P \in$ `An.dom`, the element $P(g)\cdot P(\mathrm{param})^{-\operatorname{ord}_x(\bar g)}$ of $L$ lies in $A$ and is a unit of $A$ there, where $P(\cdot)$ denotes `Place.evalAt` (the residue at $P$ pulled back to $L$ through the inverse of $L \to$ residue field of $P$) and $\operatorname{ord}$ is the normalised integer valuation of the place. Let $f \in$ `C.integers` have nonzero reduction $\bar f =$ `C.residue` $f$, with $n := \operatorname{ord}_x(\bar f) > 0$, and suppose $\operatorname{ord}_Q f = 0$ for every $Q \in$ `An.dom`. Then for every $Q \in$ `An.dom` one has $\mu(Q(f)) < 1$ and $\mu(Q(f)) = \mu(Q(\mathrm{param}))^{n}$ (an integer power).
--
--   This is the analytic form of the slope law of an attached annulus: a chart function whose reduction vanishes to positive order at the node is uniformly small, with exactly the expected slope, at every place of the tube attached at that node. It is used in the construction of component charts and annuli attached to a model, in [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentCharts_annuli_isAttached_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentCharts_annuli_isAttached_of_isModel) and its variant for the special $j$-invariants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_abv_evalAt_lt_one_of_isAttached_of_ord_residue_pos.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.Annulus.abv_evalAt_lt_one_of_isAttached_of_ord_residue_pos
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An : Annulus A F) (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar)
    (hatt : An.IsAttached C x)
    (f : F) (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (hx : 0 < x.ord (C.residue ⟨f, hf⟩)) (hzf : ∀ Q ∈ An.dom, Q.ord f = 0) :
    ∀ Q ∈ An.dom, μ (Q.evalAt f) < 1 ∧
      μ (Q.evalAt f) = μ (Q.evalAt An.param) ^ (x.ord (C.residue ⟨f, hf⟩)) := by sorry
