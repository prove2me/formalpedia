-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_conj_lie
-- name    : Formalism.FourierDecayAlt.P.Ux4.conj_lie
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:28:01.449066+00:00
-- url     : https://prove2.me/theorems/688740ec-4eca-4b8f-a670-c08e8bae923f
-- title:
--   Ux4: conj lie
-- statement:
--   The Ux4 construction uses the conj lie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L302-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L302-L315

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux4
variable {k j ρ : ℕ}

theorem Formalism.FourierDecayAlt.P.Ux4.conj_lie {N : ℕ} (n M H : Matrix (Fin N) (Fin N) ℂ) (hu : nᴴ * H * n = H) (hH : Hᴴ = H)
    (hn : n * n⁻¹ = 1) (hM : Mᴴ * H + H * M = 0) :
    (n⁻¹ * M * n)ᴴ * H + H * (n⁻¹ * M * n) = 0 := by sorry
