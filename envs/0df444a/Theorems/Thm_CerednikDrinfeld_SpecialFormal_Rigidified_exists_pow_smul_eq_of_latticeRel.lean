-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_pow_smul_eq_of_latticeRel
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_pow_smul_eq_of_latticeRel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/8ac9f803-2135-53ee-b921-453765898ded
-- title:
--   Lattice relations with equal coordinates agree up to p-power
-- statement:
--   Fix a prime $p$, a commutative ring $S$, a ring homomorphism $jS\colon \mathbb{W}(\mathbb{F}_{p^2}) \to S$ (where $\mathrm{Zp2}\ p$ is the ring of Witt vectors of the field with $p^2$ elements), and a graded Cartier module datum $E$ over $(p,S,jS)$, that is, a Witt-vector module $E.M$ equipped with Frobenius, Verschiebung and an operator $\varpi$ satisfying the usual Cartier relations together with a grading by two complementary submodules; $E.\mathrm{NMod}$ denotes the associated quotient $(E.M \times \Sigma(E))/\mathrm{nRel}$. Let $n$ be a natural number, $r\colon \mathbb{Z}_p^2 \to E.\mathrm{NMod}$ an additive map, $v \in \mathbb{Q}_p^2$, and $\zeta, \zeta' \in E.\mathrm{NMod}$. Assume both $\zeta$ and $\zeta'$ stand in the lattice relation `Rigidified.LatticeRel` to $v$ with parameters $E, n, r$: there are $m,k \in \mathbb{N}$ and $w \in \mathbb{Z}_p^2$ with $p^m v = w$ in $\mathbb{Q}_p^2$ and $p^k \cdot r(w) = p^{k+n+m} \cdot \zeta$, and likewise $m',k',w'$ with $p^{m'} v = w'$ and $p^{k'} \cdot r(w') = p^{k'+n+m'} \cdot \zeta'$. Then there exists $N \in \mathbb{N}$ with $p^N \cdot \zeta = p^N \cdot \zeta'$ (natural-number scalar multiplication in the additive group $E.\mathrm{NMod}$).
--
--   This is the uniqueness half of the rigidified coordinate description of points of the Cartier module: the element of $E.\mathrm{NMod}$ attached to a $p$-adic coordinate vector $v$ is determined by $v$ up to $p$-power torsion. It is used in [`CerednikDrinfeld.SpecialFormal.Rigidified.eq_of_isEtaSection_of_isEtaSection`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.eq_of_isEtaSection_of_isEtaSection), where the absence of $p$-torsion then upgrades the conclusion to genuine equality.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_pow_smul_eq_of_latticeRel.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega
  MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

universe u

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_pow_smul_eq_of_latticeRel
    (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] {jS : Zp2 p →+* S} (E : GradedCartierModuleData p S jS)
    (n : ℕ) (r : (Fin 2 → ℤ_[p]) →+ E.NMod) (v : Fin 2 → ℚ_[p]) (ζ ζ' : E.NMod)
    (h : Rigidified.LatticeRel E n r ζ v) (h' : Rigidified.LatticeRel E n r ζ' v) :
    ∃ N : ℕ, p ^ N • ζ = p ^ N • ζ' := by sorry
