-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_tcritPow_pos
-- name    : Formalism.FourierDecayAlt.P.Sz2.tcritPow_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:14:34.967115+00:00
-- url     : https://prove2.me/theorems/3cd23575-9920-4b7b-9513-571f9c30763c
-- title:
--   Sz2: tcrit Pow pos
-- statement:
--   The Sz2 construction uses the tcrit Pow pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CorollaryAOfPropositionA.lean#L282-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CorollaryAOfPropositionA.lean#L282-L303

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz2
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz2.tcritPow_pos {ι : Type} [Fintype ι] (S : SizeData ι) (hOk : S.Ok)
    (hds : ∀ w, 0 < S.dsig w) (w : ι) : 0 < S.TcritPow w := by sorry
