-- Prove2me | Theorems.Thm_CuspForm_exists_addMonoidHom_baseChange_intLattice_qExpansion_injective_of_ratLocalizedAt
-- name    : CuspForm.exists_addMonoidHom_baseChange_intLattice_qExpansion_injective_of_ratLocalizedAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/15670b98-cf59-531b-ac46-642fcd99fe5a
-- title:
--   ℤ₍ₚ₎-lattice of weight-two cusp forms in C[[q]]
-- statement:
--   Fix $N \ge 1$, a prime $p$, and a ring homomorphism $\iota_0 \colon \overline{\mathbf{Q}} \to \mathbf{C}$ (from `AlgebraicClosure ℚ`). Write $R =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) for the subring of $\mathbf{Q}$ consisting of the rationals whose denominator is coprime to $p$, and $S =$ [`CuspForm.intLattice N 2`](def/CuspForm_IntegralStructure.html#L3) for the $\mathbf{Z}$-submodule of weight-two cusp forms on $\Gamma_0(N)$ spanned by those forms all of whose $q$-expansion coefficients (taken with width $1$) are rational integers. The assertion is that there exists an additive map $E \colon R \otimes_{\mathbf{Z}} S \to \mathbf{C}[[q]]$ with three properties: (i) on pure tensors, $E(r \otimes f)$ is the constant power series $\iota_0(r)$, where $r \in R \subset \mathbf{Q} \subset \overline{\mathbf{Q}}$, times the $q$-expansion of $f$ of width $1$; (ii) $E$ is injective; (iii) for every weight-two cusp form $F$ on $\Gamma_0(N)$ such that each coefficient of its width-$1$ $q$-expansion lies in the image under $\iota_0$ of $R$, the $q$-expansion of $F$ lies in the image of $E$, i.e. $E(g)$ equals it for some $g \in R \otimes_{\mathbf{Z}} S$.
--
--   This is the elementary half of the integral $q$-expansion principle in weight two: the $q$-expansion map identifies $\mathbf{Z}_{(p)} \otimes_{\mathbf{Z}} S_2(\Gamma_0(N);\mathbf{Z})$ with the $\mathbf{Z}_{(p)}$-integral cusp forms inside $\mathbf{C}[[q]]$, the injectivity coming from freeness and saturation of the integral lattice and the surjectivity statement from clearing a prime-to-$p$ denominator. It is used in the comparison of the $\mathbf{Z}_{(p)}$-lattice of cusp forms with the integral de Rham / Kähler differentials of a rational model of the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_addMonoidHom_baseChange_intLattice_qExpansion_injective_of_ratLocalizedAt.lean

import Mathlib
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem CuspForm.exists_addMonoidHom_baseChange_intLattice_qExpansion_injective_of_ratLocalizedAt
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (ι₀ : AlgebraicClosure ℚ →+* ℂ) :
    ∃ E : ↥(GaloisRep.ratLocalizedAt p) ⊗[ℤ] ↥(CuspForm.intLattice N 2) →+ PowerSeries ℂ,
      (∀ (r : ↥(GaloisRep.ratLocalizedAt p)) (f : ↥(CuspForm.intLattice N 2)),
        E (r ⊗ₜ[ℤ] f) = PowerSeries.C (ι₀ (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) r)) *
          UpperHalfPlane.qExpansion 1 (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)) ∧
      Function.Injective E ∧
      (∀ F : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
        (∀ n : ℕ, ∃ r : ↥(GaloisRep.ratLocalizedAt p),
          PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 F) = ι₀ (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) r)) →
        ∃ g : ↥(GaloisRep.ratLocalizedAt p) ⊗[ℤ] ↥(CuspForm.intLattice N 2), E g = UpperHalfPlane.qExpansion 1 F) := by sorry
