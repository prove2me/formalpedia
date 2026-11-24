-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_aeval_letter_scale
-- name    : Formalism.G0.DetDividesP.aeval_letter_scale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:37.849799+00:00
-- url     : https://prove2.me/theorems/7cb0e84e-c093-40f7-b9a0-fe41bc2bc54a
-- title:
--   Det Divides P: aeval letter scale
-- statement:
--   The Det Divides P construction uses the aeval letter scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L153-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L153-L160

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
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
open Polynomial
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

theorem Formalism.G0.DetDividesP.aeval_letter_scale {B : Type} [CommSemiring B] [Algebra K B] {G : MvPolynomial (ι × Fin r) K}
    {d : ι → ℕ} (hG : MultiHom G d) (i : ι) (t : B) (z : ι × Fin r → B) :
    MvPolynomial.aeval (fun p => if p.1 = i then t * z p else z p) G = t ^ d i * MvPolynomial.aeval z G := by sorry
