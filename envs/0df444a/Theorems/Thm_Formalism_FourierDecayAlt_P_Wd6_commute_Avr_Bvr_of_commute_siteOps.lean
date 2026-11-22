-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_commute_Avr_Bvr_of_commute_siteOps
-- name    : Formalism.FourierDecayAlt.P.Wd6.commute_Avr_Bvr_of_commute_siteOps
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:40:49.223481+00:00
-- url     : https://prove2.me/theorems/3a83ccd4-672e-455e-ae86-140608311c61
-- title:
--   Wd6: commute Avr Bvr of commute site Ops
-- statement:
--   The Wd6 construction uses the commute Avr Bvr of commute site Ops property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L319-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L319-L324

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd6.commute_Avr_Bvr_of_commute_siteOps (σ : Site A) (Y : K) (z : A) (hp : Commute z σ.p) (hc : Commute z σ.c)
    (hci : Commute z σ.ci) (i j : Fin 2) : Commute z (Ts σ Y i j) := by sorry
