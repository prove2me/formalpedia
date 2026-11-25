-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_tprod_mem
-- name    : Formalism.FourierDecayAlt.P5.tprod_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:57:18.946398+00:00
-- url     : https://prove2.me/theorems/58809d59-b274-4625-aa4d-5b038dbdfd04
-- title:
--   P5: tprod mem
-- statement:
--   The P5 construction uses the tprod mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtFsvOther.lean#L288-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtFsvOther.lean#L288-L305

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtFsvOther
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate ContDiff
open Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem Formalism.FourierDecayAlt.P5.tprod_mem (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (Tc : Subalgebra ℂ (Pr (RadSp k r z z' π π')))
    (l : ℕ) (hs : ∀ l' : Fin r, l < l'.val → L.p l' ∈ Tc ∧ L.c l' ∈ Tc ∧ L.ci l' ∈ Tc) (Y : ℂ) (i : ℕ)
    (hi : l < i) : ∀ a b, tprod L Y i a b ∈ Tc := by sorry
