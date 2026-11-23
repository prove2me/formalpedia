-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_gauss7_labels
-- name    : Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.gauss7_labels
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:53.115809+00:00
-- url     : https://prove2.me/theorems/390d98ab-2f79-4cfd-a579-05bfbb7a0a2c
-- title:
--   Odd Level Gain Bounds: gauss7 labels
-- statement:
--   The Odd Level Gain Bounds construction uses the gauss7 labels property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/TwoFormsOfTheoremA.lean#L14-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/TwoFormsOfTheoremA.lean#L14-L46

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementG
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementF
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementA
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_CapLeOddShiftBound
import Definitions.Def_Formalism_GaussJetBounds_ThmAEntryFull
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_TwoFormsOfTheoremA
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
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.gauss7_labels (l d : ℕ) [NeZero d] (hl : 2 ≤ l) (TT : Finset (ZMod d))
    (nu1 size : ZMod d → ℕ) :
    ∃ (lab : ∀ s, Fin (JnumOneLetter l d TT nu1 size s) → ZMod d × ℤ) (m : ℕ),
      (∀ s, Function.Injective (lab s)) ∧
      (∀ (s s0 : ZMod d) (j : ℤ), (∃ i, lab s i = (s0, j)) ↔
        (s0 ∈ TT ∧ Odd j ∧ s = s0 + (j : ZMod d) ∧ (0 < j → l ^ j.toNat ≤ nu1 s0) ∧
          (j < 0 → l ^ (-j).toNat ≤ Dl d TT nu1 size s))) ∧
      ∀ s i, (-(lab s i).2).toNat ≤ m := by sorry
