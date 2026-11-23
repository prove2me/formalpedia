-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_dg_io
-- name    : Formalism.FourierDecayAlt.P.Fr11.dg_io
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:31:34.477224+00:00
-- url     : https://prove2.me/theorems/1de32c61-f0d4-4ea2-bd02-bf818a76d118
-- title:
--   Fr11: dg io
-- statement:
--   The Fr11 construction uses the dg io property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L49-L53

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

theorem Formalism.FourierDecayAlt.P.Fr11.dg_io (g : Ix S → ℂ) (x : A) : (dg g * io x : SlopeTestRemainingChoices S A) = io x * dg g := by sorry
