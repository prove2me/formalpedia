-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_tyS
-- name    : Formalism.L2.FormalSeriesBounds.constantCoeff_tyS
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:33:11.893683+00:00
-- url     : https://prove2.me/theorems/1e09833f-6cce-4864-8420-93e6d888ec30
-- title:
--   Formal Series Bounds: constant Coeff ty S
-- statement:
--   The Formal Series Bounds construction uses the constant Coeff ty S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffAlongCvCongr.lean#L59-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffAlongCvCongr.lean#L59-L62

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]

theorem Formalism.L2.FormalSeriesBounds.constantCoeff_tyS {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) : PowerSeries.constantCoeff (tyS l a) = 0 := by sorry
