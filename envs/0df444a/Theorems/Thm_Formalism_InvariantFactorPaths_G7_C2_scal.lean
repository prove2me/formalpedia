-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_C2_scal
-- name    : Formalism.InvariantFactorPaths.G7.C2.scal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:42:13.767699+00:00
-- url     : https://prove2.me/theorems/5088c6db-c549-4593-aead-8e509506e0cc
-- title:
--   C2: scal
-- statement:
--   The C2 construction uses the scal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TheoremCIiiMulti.lean#L16-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TheoremCIiiMulti.lean#L16-L49

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_HeckeOneLift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_GaussElementarySymmetric
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremCIiiMulti
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open CSym
open Formalism.InvariantFactorPaths.G7.C2

theorem Formalism.InvariantFactorPaths.G7.C2.scal {K : Type} [Field K] (Q N g i l : ℕ) (hQ : (Q : K) ≠ 0) (hl : l ≤ i) (a b : K)
    (hb : b ≠ 0) :
    (Q : K) ^ (-((i : ℤ) * ((N : ℤ) + g - i))) *
        (a ^ i * (Q : K) ^ (i * N) *
          (((Q ^ 2) ^ ((i - l) * (g - l)) * Formalism.G0.gaussBinom (Q ^ 2) g l : ℕ) : K) *
          (b ^ (i - l) * (Q : K) ^ ((i - l) * (N + g)))⁻¹) =
      (a / b) ^ i * eF (fun x => b * beFam (Q : K) g x) l *
        (Q : K) ^ (-(((i - l : ℕ) : ℤ) * ((N : ℤ) - (i - l : ℕ)))) := by sorry
