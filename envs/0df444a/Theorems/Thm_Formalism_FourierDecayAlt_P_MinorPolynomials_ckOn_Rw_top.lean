-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_ckOn_Rw_top
-- name    : Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_Rw_top
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:11:12.078526+00:00
-- url     : https://prove2.me/theorems/d2303cac-ec35-4f0a-a762-0faec32a6c28
-- title:
--   Minor Polynomials: ck On Rw top
-- statement:
--   The Minor Polynomials construction uses the ck On Rw top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasDerivAtEpart.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasDerivAtEpart.lean#L21-L28

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtCvs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtEpart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_Rw_top {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {UU : Set (Mat k r)} {f : Mat k r → E}
    (hf : CkOn ⊤ UU f) {w : List (Mat k r)} (hw : ∀ X ∈ w, inLie k r X) : CkOn ⊤ UU (Rw w f) := by sorry
