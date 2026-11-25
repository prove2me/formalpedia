-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_WordTransvectionCongruences_pow_apply
-- name    : Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.pow_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:32:57.162797+00:00
-- url     : https://prove2.me/theorems/70dc39fb-6948-4fc7-a5fc-ff14a4e153bd
-- title:
--   Word Transvection Congruences: pow apply
-- statement:
--   The Word Transvection Congruences construction uses the pow apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopDensNonnegOfKappa.lean#L90-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopDensNonnegOfKappa.lean#L90-L104

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDensNonnegOfKappa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped ComplexOrder ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
open Formalism.FourierDecayAlt.P5.WordTransvectionCongruences
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.pow_apply (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hAL : IsActualLevel X L) (n : ℕ) (Φ : RadSp k r z z' π π') (p : (Fin r → ℂ) × Mx k r)
    (hp : p ∈ DomR k r z z') :
    ((((L.ζ * L.ζb * L.GGi) ^ n).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) p.1 p.2 =
      (fnVal k r z z' 0 p.2 * fnVal k r z z' 2 p.2 * fnVal k r z z' 5 p.2) ^ n •
        (Φ : Fn k r (Wq →L[ℂ] Wp)) p.1 p.2 := by sorry
