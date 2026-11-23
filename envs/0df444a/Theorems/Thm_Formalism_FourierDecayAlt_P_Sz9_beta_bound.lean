-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz9_beta_bound
-- name    : Formalism.FourierDecayAlt.P.Sz9.beta_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:37:14.404812+00:00
-- url     : https://prove2.me/theorems/52aa93fe-2890-45d4-b716-58c357fc92f4
-- title:
--   Sz9: beta bound
-- statement:
--   The Sz9 construction uses the beta bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SixteenMulLeTwoPow.lean#L74-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SixteenMulLeTwoPow.lean#L74-L103

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaBoundOnBoundary
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SixteenMulLeTwoPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz9
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz9.beta_bound (hBeta : BetaOnCut) (hAZ : AZeroBound) (c : Cfg) (r : ℕ) (bb : ℝ)
    (de de' : ℕ → ℝ) (ka rd g VV T T' : ℝ) (l : ℕ)
    (hOk : c.Ok) (hm : c.m = 2 * r + 2) (hSm : c.Small bb) (hde : IsWord c.k de)
    (hde' : IsWord c.k de') (hrd : 1 ≤ rd) (hka : ka = 2 * Real.pi / rd) (hg : 2 * Real.pi ≤ g)
    (hFD : FormalDegreeLower c (1 / 2) VV) (hT : 0 < T) (hT' : 0 < T') (hl1 : 1 ≤ l)
    (hl2 : l + 2 ≤ c.k) (hdl : de l ≠ de' l) (D : ℝ) (hD : D ≤ c.Del / 2) (Y : ℝ)
    (hY1 : 5 / 2 ≤ c.v l + Y) (hY2 : c.v l + Y ≤ D) :
    0 ≤ g ^ c.m * c.be ka de de' T T' Y ∧
      g ^ c.m * c.be ka de de' T T' Y ≤
        160 * tv c de de' ka rd g VV T T' * Real.sqrt c.k * Real.sqrt (D / c.Del) := by sorry
