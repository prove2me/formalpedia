-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_aeval_weighted_scale
-- name    : Formalism.G0.DetDividesP.aeval_weighted_scale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:51.387109+00:00
-- url     : https://prove2.me/theorems/3ec59a24-c314-473b-9bc3-c5aa4287b6f2
-- title:
--   Det Divides P: aeval weighted scale
-- statement:
--   The Det Divides P construction uses the aeval weighted scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L136-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L136-L151

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

theorem Formalism.G0.DetDividesP.aeval_weighted_scale {σ : Type} {B : Type} [CommSemiring B] [Algebra K B] (w : σ → ℕ)
    {φ : MvPolynomial σ K} {n : ℕ} (hφ : MvPolynomial.IsWeightedHomogeneous w φ n) (t : B) (z : σ → B) :
    MvPolynomial.aeval (fun p => t ^ (w p) * z p) φ = t ^ n * MvPolynomial.aeval z φ := by sorry
