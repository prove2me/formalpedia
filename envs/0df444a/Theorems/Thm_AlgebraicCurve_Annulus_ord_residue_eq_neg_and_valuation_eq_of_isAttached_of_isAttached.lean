-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_ord_residue_eq_neg_and_valuation_eq_of_isAttached_of_isAttached
-- name    : AlgebraicCurve.Annulus.ord_residue_eq_neg_and_valuation_eq_of_isAttached_of_isAttached
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/c47c7052-223f-5d03-b267-126d292e75bc
-- title:
--   Opposite orders at the two ends of an annulus
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, $F$ a field extension of $L$, and $F_s$, $F_t$ fields over the residue field of $A$; let $C_s$, $C_t$ be component charts for $A$, $F$ with values in $F_s$, $F_t$ (each consisting of a valuation subring `integers` of $F$, a surjective residue homomorphism to the target field with kernel the maximal ideal, a set `dom` of places of $F/L$, a finite set of `nodes` among the places of the target field over the residue field of $A$, a map `placeMap`, and the listed compatibilities), and let $A\!n$, $A\!n'$ be annuli and $x_s$, $x_t$ places of $F_s$, $F_t$ over the residue field of $A$. Assume $A\!n'$ and $A\!n$ have the same domain and the same modulus $\mu$, that $\mu \neq 0$ in $L$, and that the product of the two parameters is the image of $\mu$ in $F$; assume $A\!n$ is attached to $(C_s,x_s)$ and $A\!n'$ to $(C_t,x_t)$, i.e. $x_s \in C_s.\mathrm{nodes}$, the parameter of $A\!n$ lies in $C_s.\mathrm{integers}$ with $\mathrm{ord}_{x_s}$ of its residue equal to $1$, and for every $f \in C_s.\mathrm{integers}$ with non-zero residue and $\mathrm{ord}_P f = 0$ at all $P$ in the domain, the element $P.\mathrm{evalAt}(f) \cdot (P.\mathrm{evalAt}(\text{param}))^{-\mathrm{ord}_{x_s}(\text{residue of } f)}$ lies in $A$ and is a unit there — and correspondingly for $A\!n'$, $C_t$, $x_t$. Assume further that two places $P_1,P_2$ of the domain give distinct values $A.\mathrm{valuation}(P_i.\mathrm{evalAt}(\text{param of } A\!n))$. Finally let $\varphi \neq 0$ satisfy $\mathrm{ord}_P \varphi = 0$ for all $P$ in the domain of $A\!n$, and let $c_s, c_t \in L$ be such that $c_s \varphi \in C_s.\mathrm{integers}$ and $c_t \varphi \in C_t.\mathrm{integers}$ have non-zero residues $\overline{c_s\varphi}$, $\overline{c_t\varphi}$. Then $\mathrm{ord}_{x_t}(\overline{c_t\varphi}) = -\,\mathrm{ord}_{x_s}(\overline{c_s\varphi})$ and $A.\mathrm{valuation}(c_t) = A.\mathrm{valuation}(c_s) \cdot A.\mathrm{valuation}(\mu)^{\mathrm{ord}_{x_t}(\overline{c_t\varphi})}$. The proof uses only the unit-normalisation clause of each attachment hypothesis, not the membership of $x_s$, $x_t$ in the respective sets of nodes nor the normalisation of the order of the residue of the parameter.
--
--   This is the edge contribution to the slope law on the dual graph of a semistable covering: a function without zeros or poles on an annulus has reductions of opposite orders at the two ends, and the two normalising constants differ by the corresponding power of the modulus. It is used in the construction of integral normalisations along semistable models, being cited by [`AlgebraicCurve.exists_forall_smul_div_pow_mem_integers_of_cartierData_of_balanced_of_semistableModel`](thm.html#AlgebraicCurve.exists_forall_smul_div_pow_mem_integers_of_cartierData_of_balanced_of_semistableModel) and [`AlgebraicCurve.exists_forall_smul_div_pow_mem_integers_of_cartierData_of_divisor_of_semistableModel`](thm.html#AlgebraicCurve.exists_forall_smul_div_pow_mem_integers_of_cartierData_of_divisor_of_semistableModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_ord_residue_eq_neg_and_valuation_eq_of_isAttached_of_isAttached.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.Annulus.ord_residue_eq_neg_and_valuation_eq_of_isAttached_of_isAttached
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fs Ft : Type*} [Field Fs] [Field Ft] [Algebra (ResidueField A) Fs] [Algebra (ResidueField A) Ft]
    (Cs : ComponentChart A F Fs) (Ct : ComponentChart A F Ft)
    (An An' : Annulus A F) (xs : Place (ResidueField A) Fs) (xt : Place (ResidueField A) Ft)
    (hpair : An'.dom = An.dom ∧ An'.modulus = An.modulus ∧ ((An.modulus : L) ≠ 0) ∧
      An'.param * An.param = algebraMap L F (An.modulus : L))
    (hatt : An.IsAttached Cs xs ∧ An'.IsAttached Ct xt)
    (hrad : ∃ P₁ ∈ An.dom, ∃ P₂ ∈ An.dom,
      A.valuation (P₁.evalAt An.param) ≠ A.valuation (P₂.evalAt An.param))
    (φ : F) (hφ0 : φ ≠ 0) (hφ : ∀ P ∈ An.dom, P.ord φ = 0)
    (cs ct : L) (hcs : cs • φ ∈ Cs.integers) (hcs' : Cs.residue ⟨cs • φ, hcs⟩ ≠ 0)
    (hct : ct • φ ∈ Ct.integers) (hct' : Ct.residue ⟨ct • φ, hct⟩ ≠ 0) :
    xt.ord (Ct.residue ⟨ct • φ, hct⟩) = -xs.ord (Cs.residue ⟨cs • φ, hcs⟩) ∧
    A.valuation ct = A.valuation cs * A.valuation (An.modulus : L) ^ xt.ord (Ct.residue ⟨ct • φ, hct⟩) := by sorry
