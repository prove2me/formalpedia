-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_Kills_mul_left
-- name    : Formalism.IrreducibleCountingLemmas.Z.BN.Kills.mul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:45:51.939507+00:00
-- url     : https://prove2.me/theorems/7eff845b-67b9-42b4-bf76-926ece0cb07d
-- title:
--   Kills: mul left
-- statement:
--   The Kills construction uses the mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L225-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean#L225-L229

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z Formalism.IrreducibleCountingLemmas.Z.BN

theorem Formalism.IrreducibleCountingLemmas.Z.BN.Kills.mul_left {K A : Type} [Field K] [Ring A] [Algebra K A] {t : Finset (A → K[X])}
    {a : A} (h : Kills t a) (b : A) : Kills t (b * a) := by sorry
