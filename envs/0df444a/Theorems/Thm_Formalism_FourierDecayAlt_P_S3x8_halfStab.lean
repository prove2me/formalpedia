-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_halfStab
-- name    : Formalism.FourierDecayAlt.P.S3x8.halfStab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:56.009907+00:00
-- url     : https://prove2.me/theorems/51c832b8-8441-4bf4-8428-910c035272f1
-- title:
--   S3x8: half Stab
-- statement:
--   The S3x8 construction uses the half Stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L641-L664
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L641-L664

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x8
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {F : Type} [Field F] {r k : ℕ}

theorem Formalism.FourierDecayAlt.P.S3x8.halfStab {g n n' : Matrix (Idx r k) (Idx r k) F}
    (hc : ∀ (l : ℕ) (hl : l ≤ r), cm (b31 g) l hl ≠ 0) (hn : IsN n) (hn' : IsN n')
    (e : g * n' = n * g) : b33 n = 1 ∧ b11 n' = 1 ∧ b23 n = 0 ∧ b12 n' = 0 := by sorry
