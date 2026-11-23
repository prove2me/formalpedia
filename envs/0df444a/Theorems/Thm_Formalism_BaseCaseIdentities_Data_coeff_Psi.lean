-- Prove2me | Theorems.Thm_Formalism_BaseCaseIdentities_Data_coeff_Psi
-- name    : Formalism.BaseCaseIdentities.Data.coeff_Psi
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:27:54.651981+00:00
-- url     : https://prove2.me/theorems/4ffcb185-fb5f-4d5d-a15b-662647dbb40b
-- title:
--   Data: coeff Psi
-- statement:
--   The Data construction uses the coeff Psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/HasUniqueFixedPoint.lean#L111-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/HasUniqueFixedPoint.lean#L111-L113

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
variable {k : Type*} [Field k] {Z : Type*} {C : Type*}
open Formalism.BaseCaseIdentities.Data
variable [Fintype Z] [Fintype C] (D : Data k Z C)

theorem Formalism.BaseCaseIdentities.Data.coeff_Psi (t : C → MvPowerSeries Z k) (b : C) (A : Z →₀ ℕ) :
    coeff A (D.Psi t b) = coeff A (D.zvec b) -
      ∑ c, ∑ j ∈ Finset.Icc 1 A.degree, D.al c j b * coeff A (t c ^ (D.l ^ j)) := by sorry
