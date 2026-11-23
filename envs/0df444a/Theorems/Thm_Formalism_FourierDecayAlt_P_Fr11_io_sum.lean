-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_io_sum
-- name    : Formalism.FourierDecayAlt.P.Fr11.io_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:19.003379+00:00
-- url     : https://prove2.me/theorems/4ed8720b-1de3-4118-9b9f-628e509492c0
-- title:
--   Fr11: io sum
-- statement:
--   The Fr11 construction uses the io sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L223-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L223-L224

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ResidueForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr11
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
noncomputable section
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Fr11.io_sum {J : Type} (s : Finset J) (x : J → A) : (io (∑ j ∈ s, x j) : SlopeTestRemainingChoices S A) = ∑ j ∈ s, io (x j) := by sorry
