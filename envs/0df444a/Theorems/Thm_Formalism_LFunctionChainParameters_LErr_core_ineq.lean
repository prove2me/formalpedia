-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LErr_core_ineq
-- name    : Formalism.LFunctionChainParameters.LErr.core_ineq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:30:22.947815+00:00
-- url     : https://prove2.me/theorems/584154b5-337f-4f89-8621-2d399d57c999
-- title:
--   LErr: core ineq
-- statement:
--   The LErr construction uses the core ineq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L13-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L13-L207

import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LErr
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem Formalism.LFunctionChainParameters.LErr.core_ineq {nT a b b' k L La B0 Nc M sA lW lk lH dI et Xpp y yD yL K h g
    cDiv cE cH cCount cSlope cSl1 cLoss : ℝ}
    (hy : 1 ≤ y) (hyD : 1 ≤ yD) (hyL : 1 ≤ yL)
    (hnT : 1 ≤ nT) (ha1 : 1 ≤ a) (hb0 : 0 ≤ b) (hba : b ≤ a) (hM : 0 ≤ M) (hk : 0 < k) (hMk : M ≤ k)
    (hMb : M * b ≤ a) (hL0 : 0 ≤ L) (hL : L ≤ 2 * y) (hLa0 : 0 ≤ La) (hLa : La ≤ 2 * y)
    (hb' : 0 ≤ b') (hkb' : k * b' ≤ a) (hX0 : 0 ≤ Xpp) (hX : Xpp ≤ a)
    (hsA0 : 0 ≤ sA) (hsA : sA ≤ 2 * (nT * a)) (hB0 : 0 ≤ B0) (hNc : 0 ≤ Nc)
    (hlW : lW ≤ a) (hlk0 : 0 ≤ lk) (hlk : lk ≤ g * y) (hlH0 : 0 ≤ lH) (hlH : lH ≤ h * y)
    (hdI0 : 0 ≤ dI) (hdI : dI ≤ 2) (het : et ≤ K * y * (nT * a))
    (c1 : 0 ≤ cDiv) (c1' : cDiv ≤ K) (c2 : 0 ≤ cE) (c2' : cE ≤ K) (c3 : 0 ≤ cH) (c3' : cH ≤ K)
    (c4 : 0 ≤ cCount) (c4' : cCount ≤ K) (c5 : 0 ≤ cSlope) (c5' : cSlope ≤ K)
    (c6 : 0 ≤ cSl1) (c6' : cSl1 ≤ K) (c7 : 0 ≤ cLoss) (c7' : cLoss ≤ K)
    (hh : 1 ≤ h) (hg : 1 ≤ g) (hbig : 200 * (1 + K) ^ 2 * h * g ≤ y) :
    sA * (cCount * (La + M ^ 2 * La / k))
      + (cDiv * nT * a * La + cDiv * M * (B0 + Nc) * yD)
      + M * cE * B0
      + cSlope * nT * a * La * (1 + M / k)
      + lW
      + cLoss * nT * M * b * yL
      + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
          + cSl1 * Xpp + 1)
      + dI * (4 * lH * ((cSlope * nT * a * La * (2 + M / k)
            + (2 * M * cE * B0 + cH * (nT * a * La + M * B0) + sA * (cCount * lk))
            + cSl1 * M * B0
            + (cSl1 * (cLoss * nT * M * b * yL) + cSl1 * nT * M * (a / k + b') * (cCount * M * L)
                + cSl1 * Xpp + 1)) + b) + et)
      ≤ yD * yL * y * y * y * (nT * a * (1 + M ^ 2 / k) + M * (B0 + Nc)) := by sorry
