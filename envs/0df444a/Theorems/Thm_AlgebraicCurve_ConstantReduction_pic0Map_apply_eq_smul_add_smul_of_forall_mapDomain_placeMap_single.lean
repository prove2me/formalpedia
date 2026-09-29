-- Prove2me | Theorems.Thm_AlgebraicCurve_ConstantReduction_pic0Map_apply_eq_smul_add_smul_of_forall_mapDomain_placeMap_single
-- name    : AlgebraicCurve.ConstantReduction.pic0Map_apply_eq_smul_add_smul_of_forall_mapDomain_placeMap_single
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/dd74d908-2001-5f7a-8481-3c8f5af2b025
-- title:
--   From place-level congruence to Pic⁰ under constant reduction
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, $F$ a field extension of $L$, and $\bar F$ a field extension of the residue field of $A$. Let $\mathcal R$ be a constant reduction datum of $F$ along $A$ onto $\bar F$: a valuation subring of $F$ whose intersection with $L$ is $A$, a surjective ring homomorphism from it to $\bar F$ with kernel the maximal ideal and compatible with the residue map of $A$, a map $P \mapsto \bar P$ from the places of $F/L$ (valuation subrings of $F$, not equal to $F$, containing the image of $L$ and with principal ideals) to the places of $\bar F$ over the residue field of $A$ preserving degrees, together with the compatibility of orders of units with residues. Let $T$ be an additive endomorphism of the divisor group $\mathrm{Div}(F/L) = (\text{places}) \to_{f} \mathbb Z$ carrying degree-zero divisors to degree-zero divisors (hypothesis $hT0$), and let $T_J$ be a self-map of $\mathrm{Pic}^0(F/L)$, the quotient of the degree-zero divisors by the principal ones, agreeing with $T$ on classes: $T_J[D] = [T D]$ for every degree-zero $D$. Let $g$ be a semilinear automorphism of $\bar F$ over the residue field of $A$, i.e. a pair consisting of a ring automorphism of $\bar F$ and one of the residue field intertwined by the structure map, and let $\ell$ be a natural number. Assume that for every place $P$ of $F/L$ the pushforward along $P \mapsto \bar P$ of $T$ applied to the divisor $1 \cdot P$ equals $1\cdot(g \bar P) + \ell \cdot (g^{-1}\bar P)$. Then for every class $c \in \mathrm{Pic}^0(F/L)$, the induced reduction map on $\mathrm{Pic}^0$ satisfies $\mathcal R_*(T_J c) = g \cdot \mathcal R_*(c) + \ell\,(g^{-1} \cdot \mathcal R_*(c))$.
--
--   This is the transport of an Eichler–Shimura type congruence from the level of individual places to the level of degree-zero divisor classes across a constant reduction: a correspondence whose reduction on points is $g + \ell g^{-1}$ induces the same relation on the reduced Picard group. It is used in the construction of the Eichler–Shimura relation for the Čerednik–Drinfeld model of a Shimura curve, where $g$ is the semilinear Frobenius of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ConstantReduction_pic0Map_apply_eq_smul_add_smul_of_forall_mapDomain_placeMap_single.lean

import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.ConstantReduction.pic0Map_apply_eq_smul_add_smul_of_forall_mapDomain_placeMap_single
    {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField ↥A) Fbar]
    (𝓡 : ConstantReduction A F Fbar)
    (T : Divisor L F →+ Divisor L F)
    (hT0 : ∀ D : Divisor L F, D ∈ Divisor.degZero (K := L) (F := F) → T D ∈ Divisor.degZero (K := L) (F := F))
    (TJ : Pic0 L F → Pic0 L F)
    (hTJ : ∀ D : Divisor.degZero (K := L) (F := F), TJ (Pic0.mk D) = Pic0.mk ⟨T (D : Divisor L F), hT0 D D.2⟩)
    (g : SemilinearAut (IsLocalRing.ResidueField ↥A) Fbar) (ℓ : ℕ)
    (hplace : ∀ P : Place L F, Finsupp.mapDomain 𝓡.placeMap (T (Finsupp.single P 1)) =
      Finsupp.single (g • 𝓡.placeMap P) 1 + ℓ • Finsupp.single (g⁻¹ • 𝓡.placeMap P) 1) :
    ∀ c : Pic0 L F, 𝓡.pic0Map (TJ c) = g • 𝓡.pic0Map c + ℓ • (g⁻¹ • 𝓡.pic0Map c) := by sorry
