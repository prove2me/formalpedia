-- Prove2me | Theorems.Thm_Formalism_DivisionValues_idxChange_at
-- name    : Formalism.DivisionValues.idxChange_at
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:05:53.167123+00:00
-- url     : https://prove2.me/theorems/b10d1dd0-b4f5-4829-af21-740605a11618
-- title:
--   Division Values: idx Change at
-- statement:
--   The Division Values construction uses the idx Change at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L671-L679
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L671-L679

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
open NumberField
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.DivisionValues.idxChange_at {d : ℕ} (v : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) (Fin d → K))
    (e : Fin d → Fin d → K) (he : LinearIndependent K e) (γ : Matrix (Fin d) (Fin d) K)
    (hγ : γ.det ≠ 0)
    (hloc : localization₂ v.asIdeal (Submodule.span (𝓞 K) (Set.range (idxChangeAct e γ))) =
      localization₂ v.asIdeal L) :
    idx v (Submodule.span (𝓞 K) (Set.range e)) L = vw v γ.det := by sorry
