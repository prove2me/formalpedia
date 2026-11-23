-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz1_vol_chain
-- name    : Formalism.FourierDecayAlt.P.Sz1.vol_chain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:32.843288+00:00
-- url     : https://prove2.me/theorems/880ca409-3691-42d8-833c-c98004b7bf7b
-- title:
--   Sz1: vol chain
-- statement:
--   The Sz1 construction uses the vol chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MassRatioFormula.lean#L67-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MassRatioFormula.lean#L67-L82

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz1
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz1.vol_chain {ι : Type} [Fintype ι] (S : SizeData ι) (hM : S.MassRatios) (d : ℕ)
    (hd : S.k + d ≤ S.n) :
    S.vol (S.k + d) =
      ((S.v / Real.pi) ^ (∑ M ∈ Ioc S.k (S.k + d), M) *
          ((∏ i ∈ Ico S.k (S.k + d), i.factorial : ℕ) : ℝ)) ^ S.f *
        (S.dF ^ (-(1 / 2 : ℝ))) ^ d * (∏ M ∈ Ioc S.k (S.k + d), S.Lv M) * S.vol S.k := by sorry
