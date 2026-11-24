-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_uh_of_herm
-- name    : Formalism.FourierDecayAlt.P.HermitianXiVector.uh_of_herm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:44:55.441281+00:00
-- url     : https://prove2.me/theorems/96fa39e2-8a06-4f52-bf6b-2c6a5361477a
-- title:
--   Hermitian Xi Vector: uh of herm
-- statement:
--   The Hermitian Xi Vector construction uses the uh of herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianXiVector.lean#L123-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianXiVector.lean#L123-L130

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

theorem Formalism.FourierDecayAlt.P.HermitianXiVector.uh_of_herm {n : ℕ} (H A : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ y y', herm H (A *ᵥ y) (A *ᵥ y') = herm H y y') : A ∈ UH H := by sorry
