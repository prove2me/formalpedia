-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableModel_exists_smul_div_pow_mem_integers_of_isPreconnected_of_fintype_mem_range
-- name    : AlgebraicCurve.SemistableModel.exists_smul_div_pow_mem_integers_of_isPreconnected_of_fintype_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/354d9de3-dd10-5845-9971-dd212f03c2f6
-- title:
--   A single constant works on every component
-- statement:
--   Let $L$ be an algebraically closed field, $A\subseteq L$ a valuation subring, and $F$ a field extension of $L$. Let $\iota_V,\iota_E$ be finite index sets, $\bar F_i$ fields over the residue field of $A$, $C_i$ a component chart for $(A,F,\bar F_i)$ for each $i\in\iota_V$, $An_e$ an annulus for each $e\in\iota_E$, together with maps $\mathrm{src},\mathrm{tgt}:\iota_E\to\iota_V$ and, for each $e$, places $xs_e$ of $\bar F_{\mathrm{src}(e)}$ and $xt_e$ of $\bar F_{\mathrm{tgt}(e)}$ over the residue field of $A$, and let $M$ be a semistable model for these data, with structure morphism `M.toBase` to $\operatorname{Spec} A$. Assume the fibre of `M.toBase` over the closed point of $\operatorname{Spec} A$, i.e. the preimage of that point under the underlying map of spaces, is preconnected. Let $k,r\in\mathbb N$, $g\in F$, let $U_a$ ($a\in\mathrm{Fin}\,r$) be open subschemes of `M.X` and $h_a\in F$, and let $c:\iota_V\to L$ take nonzero values such that: for all $i$ and $a$, if the point $\mathrm{gen}\,i$ of the model (the point whose local ring is the valuation subring $(C_i).integers$, lying over the closed point) belongs to $U_a$, then both $c_i\cdot(g/h_a^{\,k})$ and its inverse lie in $(C_i).integers$; and for every $e\in\iota_E$ the valuations of $c_{\mathrm{src}(e)}$ and $c_{\mathrm{tgt}(e)}$ with respect to $A$ agree. Then there is a nonzero $c_0\in L$, equal either to $1$ or to $c_{i_0}$ for some $i_0\in\iota_V$, such that for all $i$ and $a$ with $\mathrm{gen}\,i\in U_a$ both $c_0\cdot(g/h_a^{\,k})$ and its inverse lie in $(C_i).integers$.
--
--   The statement replaces a component-by-component choice of normalising constants by a single one: the equality of the $A$-valuations of the constants across each annulus, together with preconnectedness of the closed fibre, forces all these valuations to coincide, so one of the given constants (or $1$) makes $g/h_a^k$ a unit of the valuation subring attached to every component meeting the relevant open set. The extra information that $c_0$ is $1$ or one of the $c_i$ is what allows it to be taken over a finite level; it is used by [`AlgebraicCurve.exists_cartierData_kummer_finiteLevel_of_cartierData_of_balanced_of_semistableModel_of_descent`](thm.html#AlgebraicCurve.exists_cartierData_kummer_finiteLevel_of_cartierData_of_balanced_of_semistableModel_of_descent) and [`AlgebraicCurve.exists_cartierData_kummer_finiteLevel_of_cartierData_of_divisor_of_semistableModel_of_descent`](thm.html#AlgebraicCurve.exists_cartierData_kummer_finiteLevel_of_cartierData_of_divisor_of_semistableModel_of_descent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableModel_exists_smul_div_pow_mem_integers_of_isPreconnected_of_fintype_mem_range.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u u'

theorem AlgebraicCurve.SemistableModel.exists_smul_div_pow_mem_integers_of_isPreconnected_of_fintype_mem_range
    {L : Type u} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} [Fintype ιV] [Fintype ιE] {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt)
    (hconn : _root_.IsPreconnected (M.toBase.base ⁻¹' {IsLocalRing.closedPoint ↥A}))
    (k : ℕ) (g : F) (r : ℕ) (U : Fin r → M.X.Opens) (h : Fin r → F)
    (c : ιV → L) (hc0 : ∀ i, c i ≠ 0)
    (hcunit : ∀ i a, M.gen i ∈ U a →
      c i • (g / h a ^ k) ∈ (C i).integers ∧ (c i • (g / h a ^ k))⁻¹ ∈ (C i).integers)
    (hcslope : ∀ e', A.valuation (c (src e')) = A.valuation (c (tgt e'))) :
    ∃ c₀ : L, c₀ ≠ 0 ∧ (c₀ = 1 ∨ ∃ i₀, c₀ = c i₀) ∧ ∀ i a, M.gen i ∈ U a →
      c₀ • (g / h a ^ k) ∈ (C i).integers ∧ (c₀ • (g / h a ^ k))⁻¹ ∈ (C i).integers := by sorry
