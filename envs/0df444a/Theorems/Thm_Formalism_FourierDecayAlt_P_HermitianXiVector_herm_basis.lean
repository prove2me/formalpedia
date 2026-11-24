-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_herm_basis
-- name    : Formalism.FourierDecayAlt.P.HermitianXiVector.herm_basis
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:44:12.473812+00:00
-- url     : https://prove2.me/theorems/fec0fcad-35a9-4276-b3f3-54a952726e32
-- title:
--   Hermitian Xi Vector: herm basis
-- statement:
--   The Hermitian Xi Vector construction uses the herm basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianXiVector.lean#L115-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianXiVector.lean#L115-L121

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

theorem Formalism.FourierDecayAlt.P.HermitianXiVector.herm_basis {n : ℕ} (H A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    herm H (A *ᵥ Pi.single j 1) (A *ᵥ Pi.single i 1) = (Aᴴ * H * A) i j := by sorry
