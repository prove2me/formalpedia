-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_normW_pos
-- name    : Formalism.FourierDecayAlt.P.DualKernelLemmas.normW_pos
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:02:31.076405+00:00
-- url     : https://prove2.me/theorems/39719eab-4bf3-423c-a7f3-0efb5b305a1a
-- title:
--   Dual Kernel Lemmas: norm W pos
-- statement:
--   The Dual Kernel Lemmas construction uses the norm W pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DualKernelLemmas.lean#L141-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DualKernelLemmas.lean#L141-L147

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DualKernelLemmas
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities
open scoped Matrix

theorem Formalism.FourierDecayAlt.P.DualKernelLemmas.normW_pos {S : Type} (nn : ℝ → ℝ) (w : List (Letter ℂ S)) (h : ∀ l ∈ w, 0 < nn l.pt.re) :
    0 < normW nn w := by sorry
