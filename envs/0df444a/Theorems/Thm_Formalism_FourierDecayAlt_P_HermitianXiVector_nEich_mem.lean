-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_nEich_mem
-- name    : Formalism.FourierDecayAlt.P.HermitianXiVector.nEich_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:44:03.192906+00:00
-- url     : https://prove2.me/theorems/bbe689d8-39cd-4d43-8f91-cd6e33711985
-- title:
--   Hermitian Xi Vector: n Eich mem
-- statement:
--   The Hermitian Xi Vector construction uses the n Eich mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianXiVector.lean#L174-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianXiVector.lean#L174-L177

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagSpanVanishing
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianXiVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.HermitianXiVector
open C2x5 FlagSpanVanishing
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.HermitianXiVector.nEich_mem {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (ξ : Fin r → ℂ) :
    C2.nEich k r z ξ ∈ Nset k r := by sorry
