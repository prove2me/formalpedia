-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_halfForce
-- name    : Formalism.FourierDecayAlt.P.S3x8.halfForce
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:43.752426+00:00
-- url     : https://prove2.me/theorems/8f7d6dd0-fc59-4e3c-a990-a96f9d1e74fd
-- title:
--   S3x8: half Force
-- statement:
--   The S3x8 construction uses the half Force property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L751-L796
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L751-L796

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

theorem Formalism.FourierDecayAlt.P.S3x8.halfForce {ϖ : o} (hϖ : Irreducible ϖ) {j j' : Matrix (Idx r k) (Idx r k) o}
    {n n' : Matrix (Idx r k) (Idx r k) k0} {X : Matrix (Fin r) (Fin r) o}
    (hj : BT (j.map (IsLocalRing.residue o))) (hX : b31 j = ϖ • X)
    (hc : ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm X l hl))
    (hj' : BT (j'.map (IsLocalRing.residue o))) (hn : IsN n) (hn' : IsN n')
    (e : n * j'.map (algebraMap o k0) = j.map (algebraMap o k0) * n') :
    Integral o (b33 n) ∧ Integral o (b11 n') ∧ Integral o (b23 n) ∧ Integral o (b12 n') ∧
      ∃ X' : Matrix (Fin r) (Fin r) o, b31 j' = ϖ • X' ∧ ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm X' l hl) := by sorry
