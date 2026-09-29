-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableModel_smul_div_pow_mem_localRing_of_forall_ord_eq
-- name    : AlgebraicCurve.SemistableModel.smul_div_pow_mem_localRing_of_forall_ord_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/640b9ff5-f037-5796-9b5e-aaa8f3a0fe26
-- title:
--   Units of mathcal O_{X,x} from Gauss units and order data
-- statement:
--   Fix an algebraically closed field $L$, a valuation subring $A \subseteq L$, a field extension $F$ of $L$, index types $\iota_V,\iota_E$, fields $\bar F_i$ over the residue field of $A$, component charts $C_i$ (each carrying a valuation subring $(C_i).\mathrm{integers}$ of $F$ with a surjective residue map to $\bar F_i$), annuli $\mathrm{An}_e$, maps $\mathrm{src},\mathrm{tgt}\colon \iota_E \to \iota_V$ and marked places $x_s,x_t$, together with a semistable model $M$ for these data, with total space $M.X$ and an isomorphism $M.\mathrm{ffEquiv}$ of $F$ with the function field of $M.X$. Let $k \in \mathbb N$, let $G$ be an integer-valued function on the places of $F/L$ (valuation subrings of $F$ containing $L$, proper, with principal ideals), and let $g \in F$, $g \ne 0$, satisfy $\operatorname{ord}_P g = k\,G(P)$ for every place $P$, where $\operatorname{ord}$ is minus the logarithm of the associated adic valuation. Let $U_0,\dots,U_{r-1}$ be opens of $M.X$ and $h_0,\dots,h_{r-1}$ nonzero elements of $F$ such that $\operatorname{ord}_P(h_a) = G(P)$ whenever $M.\mathrm{pt}(P) \in U_a$. Let $c_0 \in L$ be nonzero and assume that for all $i$ and $a$ with $M.\mathrm{gen}(i) \in U_a$, both $c_0 \cdot (g/h_a^k)$ and its inverse lie in $(C_i).\mathrm{integers}$. Then for every $a$ and every $x \in U_a$, both $c_0 \cdot (g/h_a^k)$ and its inverse lie in $\mathrm{SemistableModel.localRing}\ M.X\ M.\mathrm{ffEquiv}\ x$, the subring of $F$ corresponding to the stalk of $M.X$ at $x$ inside the function field.
--
--   This is the statement that an explicitly normalised ratio $c_0\,g/h_a^k$ is a unit of the local ring at every point of the open $U_a$ of a semistable model, given that its divisor vanishes on the generic fibre over $U_a$ and that it is a unit of each Gauss valuation ring whose component generic point lies in $U_a$. It is used in the construction of Cartier data at finite Kummer level from divisor or Cartier data on a semistable model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableModel_smul_div_pow_mem_localRing_of_forall_ord_eq.lean

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

theorem AlgebraicCurve.SemistableModel.smul_div_pow_mem_localRing_of_forall_ord_eq
    {L : Type u} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt)
    (k : ℕ) (G : Place L F → ℤ) (g : F) (hg : g ≠ 0)
    (hkG : ∀ P : Place L F, P.ord g = (k : ℤ) * G P)
    (r : ℕ) (U : Fin r → M.X.Opens) (h : Fin r → F) (hh : ∀ a, h a ≠ 0)
    (hdiv : ∀ a (P : Place L F), M.pt P ∈ U a → P.ord (h a) = G P)
    (c₀ : L) (hc₀ : c₀ ≠ 0)
    (hunit : ∀ i a, M.gen i ∈ U a →
      c₀ • (g / h a ^ k) ∈ (C i).integers ∧ (c₀ • (g / h a ^ k))⁻¹ ∈ (C i).integers)
    (a : Fin r) (x : M.X) (hx : x ∈ U a) :
    c₀ • (g / h a ^ k) ∈ SemistableModel.localRing M.X M.ffEquiv x ∧
      (c₀ • (g / h a ^ k))⁻¹ ∈ SemistableModel.localRing M.X M.ffEquiv x := by sorry
