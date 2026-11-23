-- Prove2me | Theorems.Thm_Formalism_DivisionValues_lattice_fg_ne_bot
-- name    : Formalism.DivisionValues.lattice_fg_ne_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:28:19.42412+00:00
-- url     : https://prove2.me/theorems/b01c946c-bd08-421d-88e7-22871eae4415
-- title:
--   Division Values: lattice fg ne bot
-- statement:
--   The Division Values construction uses the lattice fg ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/KappaNormalise.lean#L299-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/KappaNormalise.lean#L299-L307

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_PassageScaleFree
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues

theorem Formalism.DivisionValues.lattice_fg_ne_bot {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {D : ℕ}
    (hD : 0 < D) (R : Submodule (𝓞 K) (Fin D → K)) (hR : Submodule.IsLattice K R) :
    R.FG ∧ R ≠ ⊥ := by sorry
