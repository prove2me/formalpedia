-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_ins_upper
-- name    : Formalism.FourierDecayAlt.P.Fr11.ins_upper
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:38.982623+00:00
-- url     : https://prove2.me/theorems/e349060b-cb93-4365-9ae2-fa06ce1434e2
-- title:
--   Fr11: ins upper
-- statement:
--   The Fr11 construction uses the ins upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L214-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L214-L216

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

theorem Formalism.FourierDecayAlt.P.Fr11.ins_upper (a : S) (p q s : SlopeTestRemainingChoices S A) :
    ins a !![p, q; 0, s] = eU a 0 0 * p + eU a 0 1 * q + eU a 1 1 * s := by sorry
