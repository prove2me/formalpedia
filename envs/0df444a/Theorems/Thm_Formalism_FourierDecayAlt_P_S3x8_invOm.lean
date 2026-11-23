-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_invOm
-- name    : Formalism.FourierDecayAlt.P.S3x8.invOm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:15:40.7224+00:00
-- url     : https://prove2.me/theorems/31a4bee6-0103-4b0a-b781-d48e41ef43fc
-- title:
--   S3x8: inv Om
-- statement:
--   The S3x8 construction uses the inv Om property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L799-L832
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L799-L832

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
variable {o : Type} [CommRing o] {k0 : Type} [Field k0] [Algebra o k0] {r k : ℕ}
variable [IsDomain o] [IsDiscreteValuationRing o] [IsFractionRing o k0]
omit [IsFractionRing o k0]

theorem Formalism.FourierDecayAlt.P.S3x8.invOm {ϖ : o} (hϖ : Irreducible ϖ) {j : Matrix (Idx r k) (Idx r k) o}
    {X : Matrix (Fin r) (Fin r) o} (hd : IsUnit j.det)
    (hj : BT (j.map (IsLocalRing.residue o))) (hX : b31 j = ϖ • X)
    (hc : ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm X l hl)) :
    BT (j⁻¹.map (IsLocalRing.residue o)) ∧
      ∃ Y : Matrix (Fin r) (Fin r) o, b31 j⁻¹ = ϖ • Y ∧ ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm Y l hl) := by sorry
