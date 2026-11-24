-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_aeval_set_scale
-- name    : Formalism.G0.DetDividesP.aeval_set_scale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:51.881694+00:00
-- url     : https://prove2.me/theorems/02bd2e9d-9f03-4a4e-9640-01d3e683895f
-- title:
--   Det Divides P: aeval set scale
-- statement:
--   The Det Divides P construction uses the aeval set scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L162-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L162-L176

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

theorem Formalism.G0.DetDividesP.aeval_set_scale {B : Type} [CommSemiring B] [Algebra K B] {G : MvPolynomial (ι × Fin r) K}
    {d : ι → ℕ} (hG : MultiHom G d) (U : Finset ι) (t : B) (z : ι × Fin r → B) :
    MvPolynomial.aeval (fun p => if p.1 ∈ U then t * z p else z p) G =
      t ^ (∑ i ∈ U, d i) * MvPolynomial.aeval z G := by sorry
