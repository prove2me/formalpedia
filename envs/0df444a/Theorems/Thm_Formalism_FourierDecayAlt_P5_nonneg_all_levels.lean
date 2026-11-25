-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_nonneg_all_levels
-- name    : Formalism.FourierDecayAlt.P5.nonneg_all_levels
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:54:06.383985+00:00
-- url     : https://prove2.me/theorems/306e6149-5602-4385-b3b8-1a12445e1fed
-- title:
--   P5: nonneg all levels
-- statement:
--   The P5 construction uses the nonneg all levels property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EqOfContinuousOffZero.lean#L63-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EqOfContinuousOffZero.lean#L63-L99

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqOfContinuousOffZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

theorem Formalism.FourierDecayAlt.P5.nonneg_all_levels {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S]
    [DecidableEq S] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (hTI : TopIdent (S := S) P z z' π π' μ L st K l0) (hTN : TopDensNonneg (S := S) P z z' π π' L st K l0)
    (hSI : SliceIn (S := S) P z z' π π' L st K l0) (hSD : StepDens (S := S) P z z' π π' μ L st K l0)
    (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w) :
    ∀ (n : ℕ) (i : Fin (P.r + 1)), i.val + n = P.r → ∀ c ∈ OmX P.r,
      ∀ x : Ix S → RadSp P.k P.r z z' π π', InK (K i) x → 0 ≤ RRform L st μ i w x x c := by sorry
