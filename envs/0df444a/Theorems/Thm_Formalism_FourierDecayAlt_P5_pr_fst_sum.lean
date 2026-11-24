-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_fst_sum
-- name    : Formalism.FourierDecayAlt.P5.pr_fst_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:42:13.58588+00:00
-- url     : https://prove2.me/theorems/07b7a46b-615d-480a-aaa3-b4549c726627
-- title:
--   P5: pr fst sum
-- statement:
--   The P5 construction uses the pr fst sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMemMatrixAlgebra.lean#L128-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMemMatrixAlgebra.lean#L128-L135

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P5.pr_fst_sum {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (s : Finset ι) (g : ι → Pr V) :
    (∑ i ∈ s, g i).1 = ∑ i ∈ s, (g i).1 := by sorry
