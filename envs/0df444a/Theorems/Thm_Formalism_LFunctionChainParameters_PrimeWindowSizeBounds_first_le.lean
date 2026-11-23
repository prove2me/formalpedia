-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_first_le
-- name    : Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.first_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:59.921485+00:00
-- url     : https://prove2.me/theorems/f3f06341-8609-48f4-989f-7511e08c5ce3
-- title:
--   Prime Window Size Bounds: first le
-- statement:
--   The Prime Window Size Bounds construction uses the first le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L1036-L1100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L1036-L1100

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

theorem Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.first_le {C₁ : ℝ}
    (hC₁ : ∀ (e J : ℕ) (Y X' ρ p₀ : ℝ) (s : Finset ℕ), 1 ≤ e → 1 ≤ J → 1 ≤ Y →
      0 ≤ ρ → ρ ≤ 1 / 2 → 8 ≤ p₀ → 2 ≤ X' →
      (∀ p ∈ s, p.Prime ∧ p ≠ 2 ∧
        (((p : ℝ) ≤ Y ∧ ∃ hl : Nat.Coprime p (4 * 2 ^ e), orderOf (Formalism.RankGapBounds.LocalQuadraticParts.hOf e p hl) ≤ J) ∨
          (p₀ ≤ p ∧ ∃ i : ℕ, 1 ≤ i ∧ X' * (1 - ρ) ≤ (p : ℝ) ^ i ∧ (p : ℝ) ^ i ≤ X' * (1 + ρ)))) →
      ∑ p ∈ s, Real.log p / p ≤
        C₁ * J * Real.log (2 ^ e * Y) ^ 2 / (2 : ℝ) ^ e +
          (⌊Real.log X'⌋₊ : ℝ) * ((4 * ρ + 1 / p₀) * Real.log (2 * X')))
    {P : Par} {e K : ℝ} (hCord : C₁ ≤ P.Cord) (hW : Windows P e K) (hL : LargeX P.x P.ε e K)
    (Ps : Finset ℕ) (cl : ℕ → PClass) (hPs : ∀ p ∈ Ps, p.Prime ∧ p ≠ 2) (hF : FirstHyp P Ps cl)
    (m T : ℝ) (hm : 0 ≤ m) (hT : 0 ≤ T) :
    4 * m * T * P.a * (∑ p ∈ Ps.filter (fun p => cl p = PClass.first), Real.log p / p) ≤
      tOrders P m T + tBand P m T := by sorry
