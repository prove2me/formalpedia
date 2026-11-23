-- Prove2me | Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_pderiv_subst_coe
-- name    : Formalism.ELL.SubstitutionCoefficientCongruence.pderiv_subst_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:19:17.382805+00:00
-- url     : https://prove2.me/theorems/02b9de12-79c9-46aa-86ed-2ff26f4ebaac
-- title:
--   Substitution Coefficient Congruence: pderiv subst coe
-- statement:
--   The Substitution Coefficient Congruence construction uses the pderiv subst coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/NDeriv.lean#L45-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/NDeriv.lean#L45-L63

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.ELL Formalism.ELL.SubstitutionCoefficientCongruence
variable {R : Type*} [CommRing R] {σ : Type*}

theorem Formalism.ELL.SubstitutionCoefficientCongruence.pderiv_subst_coe (p : Polynomial R) {a : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (i : σ) :
    MvPowerSeries.pderiv R i ((p : PowerSeries R).subst a) =
      (derivative R (p : PowerSeries R)).subst a * MvPowerSeries.pderiv R i a := by sorry
