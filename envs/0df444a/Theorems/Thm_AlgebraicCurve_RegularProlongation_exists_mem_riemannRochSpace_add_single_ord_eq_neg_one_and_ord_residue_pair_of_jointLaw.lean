-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_mem_riemannRochSpace_add_single_ord_eq_neg_one_and_ord_residue_pair_of_jointLaw
-- name    : AlgebraicCurve.RegularProlongation.exists_mem_riemannRochSpace_add_single_ord_eq_neg_one_and_ord_residue_pair_of_jointLaw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/8b205a2e-6f15-5d83-9af0-5b97fce2d89b
-- title:
--   Perturbing a simple pole to residue orders (-1,0) or (0,-1)
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, $F$ a field extension of $L$, and $K$, $\bar F$ fields with $\bar F$ an algebra over $K$ and over the residue field of $A$. Let $R_1, R_2$ be regular prolongations of $A$ to $F$ with values in $\bar F$: each consists of a valuation subring $R_i.\text{integers}$ of $F$ and a surjective ring homomorphism $R_i.\text{residue}$ onto $\bar F$ whose kernel is the maximal ideal, such that an element of $L$ lies in $A$ exactly when its image lies in $R_i.\text{integers}$, the residue map is compatible with the residue map of $A$, and every non-zero $f \in F$ has an $L$-multiple lying in $R_i.\text{integers}$ with non-zero residue. Let $E$ be a divisor of $F$ over $L$ (a finitely supported $\mathbb{Z}$-valued function on places, a place being a proper valuation subring of $F$ containing $L$ whose ring is a principal ideal ring), let $V_0$ be a place with $E(V_0) = 0$, and let $v_1, v_2$ be places of $\bar F$ over $K$; membership of $g$ in $\operatorname{riemannRochSpace} D$ means $v(g) \le \exp(D(v))$ for the adic valuation at every place $v$, i.e. $\operatorname{ord}_v g \ge -D(v)$. Assume the joint law: for every $g \in \operatorname{riemannRochSpace}(E + V_0)$ lying in both $R_i.\text{integers}$ and with both residues $\bar g_i = R_i.\text{residue}(g)$ non-zero, $-1 \le \operatorname{ord}_{v_1} \bar g_1 + \operatorname{ord}_{v_2} \bar g_2$. Assume further given $p_1 \in \operatorname{riemannRochSpace} E$, lying in both $R_i.\text{integers}$, with $\bar p_{1,1} \ne 0$, $\operatorname{ord}_{v_1} \bar p_{1,1} = 0$, and either $\bar p_{1,2} = 0$ or $\operatorname{ord}_{v_2} \bar p_{1,2} \ge 0$; symmetrically $p_2 \in \operatorname{riemannRochSpace} E$ in both rings with $\bar p_{2,2} \ne 0$, $\operatorname{ord}_{v_2} \bar p_{2,2} = 0$, and either $\bar p_{2,1} = 0$ or $\operatorname{ord}_{v_1} \bar p_{2,1} \ge 0$; and $f \in \operatorname{riemannRochSpace}(E + V_0)$ in both rings with $\operatorname{ord}_{V_0} f = -1$ violating the order bound on one side, namely $\bar f_1 \ne 0$ with $\operatorname{ord}_{v_1} \bar f_1 < 0$, or $\bar f_2 \ne 0$ with $\operatorname{ord}_{v_2} \bar f_2 < 0$. Then there exists $g \in F$ lying in both $R_i.\text{integers}$ and in $\operatorname{riemannRochSpace}(E + V_0)$, with $\operatorname{ord}_{V_0} g = -1$, both residues $\bar g_1, \bar g_2$ non-zero, and $(\operatorname{ord}_{v_1} \bar g_1, \operatorname{ord}_{v_2} \bar g_2)$ equal to $(-1,0)$ or to $(0,-1)$.
--
--   This is the perturbation step in the construction of a function with a simple pole at a chosen place which is simultaneously a unit for two regular prolongations, the two prolongations playing the role of two components of a special fibre and the joint law encoding the order law at the pair of fibre places $v_1, v_2$. It is stated for an arbitrary pair of regular prolongations and is used by [`ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_commonUnit_pole_of_reduceFst_fixed_of_isAffinePlace_of_regularityLaw_of_coe_of_unit_of_cusp_of_orient`](thm.html#ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_commonUnit_pole_of_reduceFst_fixed_of_isAffinePlace_of_regularityLaw_of_coe_of_unit_of_cusp_of_orient) in the place-specialisation analysis of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_mem_riemannRochSpace_add_single_ord_eq_neg_one_and_ord_residue_pair_of_jointLaw.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_mem_riemannRochSpace_add_single_ord_eq_neg_one_and_ord_residue_pair_of_jointLaw
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {K Fb : Type*} [Field K] [Field Fb] [Algebra K Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (R₁ R₂ : RegularProlongation A F Fb)
    (E : Divisor L F) (V₀ : Place L F) (hEV₀ : E V₀ = 0)
    (v₁ v₂ : Place K Fb)
    (hlaw : ∀ (g : F) (hg₁ : g ∈ R₁.integers) (hg₂ : g ∈ R₂.integers),
      g ∈ riemannRochSpace (E + Finsupp.single V₀ 1) →
        R₁.residue ⟨g, hg₁⟩ ≠ 0 → R₂.residue ⟨g, hg₂⟩ ≠ 0 →
          -1 ≤ v₁.ord (R₁.residue ⟨g, hg₁⟩) + v₂.ord (R₂.residue ⟨g, hg₂⟩))
    (p₁ : F) (hp₁E : p₁ ∈ riemannRochSpace E) (hp₁₁ : p₁ ∈ R₁.integers) (hp₁₂ : p₁ ∈ R₂.integers)
    (hp₁ : R₁.residue ⟨p₁, hp₁₁⟩ ≠ 0 ∧ v₁.ord (R₁.residue ⟨p₁, hp₁₁⟩) = 0 ∧
      (R₂.residue ⟨p₁, hp₁₂⟩ = 0 ∨ 0 ≤ v₂.ord (R₂.residue ⟨p₁, hp₁₂⟩)))
    (p₂ : F) (hp₂E : p₂ ∈ riemannRochSpace E) (hp₂₁ : p₂ ∈ R₁.integers) (hp₂₂ : p₂ ∈ R₂.integers)
    (hp₂ : R₂.residue ⟨p₂, hp₂₂⟩ ≠ 0 ∧ v₂.ord (R₂.residue ⟨p₂, hp₂₂⟩) = 0 ∧
      (R₁.residue ⟨p₂, hp₂₁⟩ = 0 ∨ 0 ≤ v₁.ord (R₁.residue ⟨p₂, hp₂₁⟩)))
    (f : F) (hfE : f ∈ riemannRochSpace (E + Finsupp.single V₀ 1))
    (hfV₀ : V₀.ord f = -1) (hf₁ : f ∈ R₁.integers) (hf₂ : f ∈ R₂.integers)
    (hviol : (R₁.residue ⟨f, hf₁⟩ ≠ 0 ∧ v₁.ord (R₁.residue ⟨f, hf₁⟩) < 0) ∨
      (R₂.residue ⟨f, hf₂⟩ ≠ 0 ∧ v₂.ord (R₂.residue ⟨f, hf₂⟩) < 0)) :
    ∃ (g : F) (hg₁ : g ∈ R₁.integers) (hg₂ : g ∈ R₂.integers),
      g ∈ riemannRochSpace (E + Finsupp.single V₀ 1) ∧ V₀.ord g = -1 ∧
      R₁.residue ⟨g, hg₁⟩ ≠ 0 ∧ R₂.residue ⟨g, hg₂⟩ ≠ 0 ∧
      ((v₁.ord (R₁.residue ⟨g, hg₁⟩) = -1 ∧ v₂.ord (R₂.residue ⟨g, hg₂⟩) = 0) ∨
        (v₁.ord (R₁.residue ⟨g, hg₁⟩) = 0 ∧ v₂.ord (R₂.residue ⟨g, hg₂⟩) = -1)) := by sorry
