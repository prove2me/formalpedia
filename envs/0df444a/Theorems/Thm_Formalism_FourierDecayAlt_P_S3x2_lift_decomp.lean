-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_lift_decomp
-- name    : Formalism.FourierDecayAlt.P.S3x2.lift_decomp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:16.786639+00:00
-- url     : https://prove2.me/theorems/4a6baab4-16f2-4dc1-a2d3-9d8ba7c30a2c
-- title:
--   S3x2: lift decomp
-- statement:
--   The S3x2 construction uses the lift decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L382-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L382-L403

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x2
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3
variable (o : Type) [CommRing o] [IsLocalRing o]
local notation "𝔽" => IsLocalRing.ResidueField o
variable {o} {r k : ℕ}

theorem Formalism.FourierDecayAlt.P.S3x2.lift_decomp (x : GL (Idx r k) o) (nb : GL (Idx r k) 𝔽) (hb : GL (Fin k) 𝔽)
    (hn : IsN (nb : Matrix (Idx r k) (Idx r k) 𝔽)) (hx : red o (Idx r k) x = nb * phi 𝔽 r k hb) :
    ∃ (n κ : GL (Idx r k) o) (h : GL (Fin k) o), IsN (n : Matrix (Idx r k) (Idx r k) o) ∧
      red o (Fin k) h = hb ∧ κ ∈ (red o (Idx r k)).ker ∧ x = n * phi o r k h * κ := by sorry
