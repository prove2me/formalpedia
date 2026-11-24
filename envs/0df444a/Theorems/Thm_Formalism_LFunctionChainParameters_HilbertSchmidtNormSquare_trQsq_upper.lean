-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_trQsq_upper
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.trQsq_upper
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:29.532272+00:00
-- url     : https://prove2.me/theorems/2bcf6fb3-c4cd-4e32-8583-681612e67f55
-- title:
--   Hilbert Schmidt Norm Square: tr Qsq upper
-- statement:
--   The Hilbert Schmidt Norm Square construction uses the tr Qsq upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L222-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L222-L281

import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
variable {ι : Type} [Fintype ι] {D : ℕ} {d : ι → ℕ}

theorem Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.trQsq_upper (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u)
    {Dstar η0 e0 : ℝ} (hD : 0 < Dstar) (hη : -1 ≤ η0) (he : 0 ≤ e0)
    (hP : ∀ u u', u ≠ u' → hsSq (Kp B ga u u') ≤ (1 + η0) * (d u : ℝ) * (d u' : ℝ) / Dstar)
    (hK : ∀ u, hsSq (Kd B ga u - 1) ≤ e0 * (d u : ℝ)) :
    (Qm B ga * Qm B ga).trace.re ≤ (1 + η0) * Rs d ^ 2 / Dstar + (1 + Real.sqrt e0) ^ 2 * Rs d := by sorry
