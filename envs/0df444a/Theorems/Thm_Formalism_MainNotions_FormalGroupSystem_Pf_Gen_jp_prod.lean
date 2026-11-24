-- Prove2me | Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_jp_prod
-- name    : Formalism.MainNotions.FormalGroupSystem.Pf.Gen.jp_prod
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:54:02.308652+00:00
-- url     : https://prove2.me/theorems/850248b8-9377-4e48-8456-e5cb7b8e9199
-- title:
--   Gen: jp prod
-- statement:
--   The Gen construction uses the jp prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/CoeffProdRename.lean#L148-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/CoeffProdRename.lean#L148-L168

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_CoeffProdRename
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.FormalGroupSystem.Pf Formalism.MainNotions.FormalGroupSystem.Pf.Gen
open Finset

theorem Formalism.MainNotions.FormalGroupSystem.Pf.Gen.jp_prod {K A Pl : Type} [CommRing K] [CommRing A] [Algebra K A] [Fintype Pl] [DecidableEq Pl] {ι : Pl → Type}
    [∀ v, Fintype (ι v)] (P : ∀ v, MvPolynomial (ι v) A) (g : ∀ v, MvPowerSeries (ι v) K) :
    jp (∏ v, MvPolynomial.rename (Sigma.mk v) (P v)) (∏ v, atP v (g v)) = ∏ v, jp (P v) (g v) := by sorry
