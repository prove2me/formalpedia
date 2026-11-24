-- Prove2me | Theorems.Thm_Formalism_ZF_ComplexPowerDifferenceIntegral_partial_dz
-- name    : Formalism.ZF.ComplexPowerDifferenceIntegral.partial_dz
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:41:46.171435+00:00
-- url     : https://prove2.me/theorems/f72e6b5d-de66-4493-9f01-254336193216
-- title:
--   Complex Power Difference Integral: partial dz
-- statement:
--   The Complex Power Difference Integral construction uses the partial dz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/RiemannZetaOneEqOneSubOfRePos.lean#L11-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/RiemannZetaOneEqOneSubOfRePos.lean#L11-L21

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_DzDifferentiableOn
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RiemannZetaOneEqOneSubOfRePos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZF
open Formalism.ZF.ComplexPowerDifferenceIntegral

theorem Formalism.ZF.ComplexPowerDifferenceIntegral.partial_dz (s : ℂ) (N : ℕ) :
    ∑ i ∈ Finset.range N, dz s i =
      1 - (((N : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s) -
        (s - 1) * ∑ i ∈ Finset.range N, ((((i : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (-s) := by sorry
