-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_chord_bounds_and_rigid_of_isAttached_both_ends_of_twist
-- name    : AlgebraicCurve.Annulus.chord_bounds_and_rigid_of_isAttached_both_ends_of_twist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/143db87f-3844-5103-8bba-0fbf9ac99c01
-- title:
--   Twisted chord bounds and rigidity on a doubly attached annulus
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, and $F$ a field extension of $L$ in which every nonzero element has a principal divisor of degree zero (`HasPrincipalDivisors`); let $\bar F$ and $\bar F'$ be extensions of the residue field of $A$. Let $\mu$ be a real absolute value on $L$ whose unit ball is exactly $A$. Let $An$, $An'$ be annuli in $F$ over $A$ — each consisting of a set of places of $F/L$, a parameter, and a modulus in the maximal ideal of $A$, subject to the axioms of `Annulus` (rationality and parameter conditions on the domain, uniqueness of a place with prescribed parameter value, order one for $\mathrm{param} - \mathrm{param}(P)$, and the unit principle) — with the same domain, the same modulus $\pi$, with $\pi \neq 0$ in $L$, and with $An'.\mathrm{param} \cdot An.\mathrm{param} = \pi$ in $F$; write $z$ for $An.\mathrm{param}$. Let $C$ be a component chart over $\bar F$ and $x$ a place of $\bar F$ over the residue field of $A$ with $An$ attached to $C$ at $x$, i.e. $x$ is a node of $C$, $z$ lies in $C.\mathrm{integers}$ with $\mathrm{ord}_x$ of its residue equal to $1$, and for every $g \in C.\mathrm{integers}$ with nonzero residue and $\mathrm{ord}_P g = 0$ throughout $An.\mathrm{dom}$ the element $g(P) \, z(P)^{-\mathrm{ord}_x(\bar g)}$ is a unit of $A$ at each $P \in An.\mathrm{dom}$; likewise let $An'$ be attached to a chart $C'$ over $\bar F'$ at a place $x'$. Here $g(P) = P.\mathrm{evalAt}\, g$ denotes the element of $L$ representing the residue of $g$ at $P$ (and $0$ if $g$ is not $P$-integral). Assume the annulus is wide: $\mu(z(Q_1)) \neq \mu(z(Q_2))$ for some $Q_1, Q_2 \in An.\mathrm{dom}$. Let $f \in C.\mathrm{integers}$ have nonzero residue, and let $c' \in L$ be nonzero with $c'^{-1} f \in C'.\mathrm{integers}$ of nonzero residue. Let $D$ be a finitely supported integer-valued function on the places of $F/L$, supported in $An.\mathrm{dom}$, and set $h = f \prod_{R \in \mathrm{supp}\,D} (z - z(R))^{D(R)}$; assume $\mathrm{ord}_P h \ge 0$ for every $P \in An.\mathrm{dom}$. Put $o_1 = \mathrm{ord}_x(C.\mathrm{residue}(f))$, $o_2 = \mathrm{ord}_{x'}(C'.\mathrm{residue}(c'^{-1}f))$, $M = \sum_R D(R)$ and $\Lambda = \prod_R \mu(z(R))^{D(R)}$. Then $\mu(\pi)^{o_1 + M} \le \mu(c')\Lambda$ and $\mu(c')\Lambda\,\mu(\pi)^{o_2} \le 1$, and if either of these two inequalities is an equality, then $\mathrm{ord}_P h = 0$ for every $P \in An.\mathrm{dom}$ and $o_1 + M + o_2 = 0$.
--
--   This is the non-archimedean Jensen-type estimate for a function on an annulus read from both ends: the total increment of the piecewise-linear valuation profile of $h$ across the annulus is squeezed between the two end tangents, and equality forces $h$ to be zero-free with matching near and far slopes. It is invoked in the valuation estimates for prolongation tuples on modular curves, in [`ModularCurve.PlaceSpecialization.ProlongationTuple.valuation_pow_le_mul_prod_and_rigid_of_twist`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.valuation_pow_le_mul_prod_and_rigid_of_twist) and its level-one variant; it combines the two one-sided bounds [`AlgebraicCurve.Annulus.abv_modulus_zpow_ord_residue_le_abv_of_isAttached_both_ends`](thm.html#AlgebraicCurve.Annulus.abv_modulus_zpow_ord_residue_le_abv_of_isAttached_both_ends) and [`AlgebraicCurve.Annulus.abv_mul_abv_modulus_zpow_ord_residue_le_one_of_isAttached_both_ends`](thm.html#AlgebraicCurve.Annulus.abv_mul_abv_modulus_zpow_ord_residue_le_one_of_isAttached_both_ends) with the slope identity [`AlgebraicCurve.Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends`](thm.html#AlgebraicCurve.Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_chord_bounds_and_rigid_of_isAttached_both_ends_of_twist.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.Annulus.chord_bounds_and_rigid_of_isAttached_both_ends_of_twist
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    [HasPrincipalDivisors L F]
    {Fbar Fbar' : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [Field Fbar'] [Algebra (ResidueField A) Fbar']
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An An' : Annulus A F) (hdom : An'.dom = An.dom) (hmod : An'.modulus = An.modulus)
    (hmod0 : (An.modulus : L) ≠ 0)
    (htwo : An'.param * An.param = algebraMap L F (An.modulus : L))
    (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar) (hatt : An.IsAttached C x)
    (C' : ComponentChart A F Fbar') (x' : Place (ResidueField A) Fbar') (hatt' : An'.IsAttached C' x')
    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, μ (Q₁.evalAt An.param) ≠ μ (Q₂.evalAt An.param))
    (f : F) (hC : f ∈ C.integers) (hres : C.residue ⟨f, hC⟩ ≠ 0)
    (c' : L) (hc'0 : c' ≠ 0)
    (hC' : (algebraMap L F c')⁻¹ * f ∈ C'.integers) (hres' : C'.residue ⟨(algebraMap L F c')⁻¹ * f, hC'⟩ ≠ 0)
    (D : Place L F →₀ ℤ) (hD : ∀ P, D P ≠ 0 → P ∈ An.dom)
    (hpole : ∀ P ∈ An.dom, 0 ≤ P.ord (f * ∏ R ∈ D.support, (An.param - algebraMap L F (R.evalAt An.param)) ^ D R)) :
    μ (An.modulus : L) ^ (x.ord (C.residue ⟨f, hC⟩) + ∑ R ∈ D.support, D R)
        ≤ μ c' * ∏ R ∈ D.support, μ (R.evalAt An.param) ^ D R ∧
      μ c' * (∏ R ∈ D.support, μ (R.evalAt An.param) ^ D R)
          * μ (An.modulus : L) ^ (x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * f, hC'⟩)) ≤ 1 ∧
      ((μ (An.modulus : L) ^ (x.ord (C.residue ⟨f, hC⟩) + ∑ R ∈ D.support, D R)
            = μ c' * ∏ R ∈ D.support, μ (R.evalAt An.param) ^ D R ∨
        μ c' * (∏ R ∈ D.support, μ (R.evalAt An.param) ^ D R)
            * μ (An.modulus : L) ^ (x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * f, hC'⟩)) = 1) →
        (∀ P ∈ An.dom, P.ord (f * ∏ R ∈ D.support, (An.param - algebraMap L F (R.evalAt An.param)) ^ D R) = 0) ∧
          x.ord (C.residue ⟨f, hC⟩) + (∑ R ∈ D.support, D R) + x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * f, hC'⟩) = 0) := by sorry
