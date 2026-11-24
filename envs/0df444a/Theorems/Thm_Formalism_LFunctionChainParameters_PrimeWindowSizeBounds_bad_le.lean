-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_bad_le
-- name    : Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.bad_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:03.754081+00:00
-- url     : https://prove2.me/theorems/d4950791-1fc1-4f2b-af4b-4911e8d54764
-- title:
--   Prime Window Size Bounds: bad le
-- statement:
--   The Prime Window Size Bounds construction uses the bad le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L988-L1034
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L988-L1034

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr

theorem Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.bad_le {τ : Type} (P : Par) (Ps sB : Finset ℕ) (cl : ℕ → PClass) (TT : Finset τ)
    (TTp : ℕ → Finset τ) (BAD : ℕ → τ → Prop) (m : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ P.a) (hβ : 0 ≤ P.β)
    (hX : 1 ≤ P.Xp) (hsB : ∀ p ∈ sB, p.Prime ∧ (p : ℝ) ≤ P.Xp)
    (hTops : ∑ p ∈ sB, 4 * m * P.a * (Real.log p / p) * ((TT.filter fun t => BAD p t).card : ℝ) ≤
      32 * P.β * m * P.a * TT.card * ∑ p ∈ sB, Real.log p / p)
    (hBad : ∀ p ∈ Ps, cl p = PClass.served → ∀ t ∈ TT \ TTp p, p ∈ sB ∧ BAD p t) :
    ∑ p ∈ Ps.filter (fun p => cl p = PClass.served),
      4 * m * P.a * (Real.log p / p) * ((TT \ TTp p).card : ℝ) ≤ tBad P m TT.card := by sorry
