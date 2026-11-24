-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_descent
-- name    : Formalism.MainNotions.J.descent
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T09:56:40.472531+00:00
-- url     : https://prove2.me/theorems/b867c4ca-b49c-4a0a-b394-10874bcd3ce4
-- title:
--   J: descent
-- statement:
--   The J construction uses the descent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L409-L429
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L409-L429

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_GandSo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open MvPowerSeries
variable {ι κ : Type} {K : Type} [Field K]

theorem Formalism.MainNotions.J.descent (O : Subring K) (th lg ps : PowerSeries K) (hth0 : PowerSeries.constantCoeff th = 0)
    (hps0 : PowerSeries.constantCoeff ps = 0) (hpsO : ∀ n, PowerSeries.coeff n ps ∈ O)
    (hinv : PowerSeries.subst ps th = PowerSeries.X) (hlg0 : PowerSeries.constantCoeff lg = 0)
    (G : MvPowerSeries ι K) (h : ∀ n, coeff n (subst (diagS (PowerSeries.subst th lg)) G) ∈ O) :
    ∀ n, coeff n (subst (diagS lg) G) ∈ O := by sorry
