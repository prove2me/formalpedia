-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DeterminantVectorSums_main
-- name    : Formalism.FourierDecayAlt.P.DeterminantVectorSums.main
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:38:57.036888+00:00
-- url     : https://prove2.me/theorems/1c03f163-7728-4616-92de-f5e8d296f8c9
-- title:
--   Determinant Vector Sums: main
-- statement:
--   The Determinant Vector Sums construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StarSumLemmas.lean#L257-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StarSumLemmas.lean#L257-L332

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StarSumLemmas
import Theorems.Thm_Formalism_FourierDecayAlt_Q_Adapted_main
import Theorems.Thm_PI_QmLemDWork_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DeterminantVectorSums
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} (E : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V)

theorem Formalism.FourierDecayAlt.P.DeterminantVectorSums.main (hQ : QminorPoly) (hPV : PolyVanish) (y : Fin (N + 1) → Module.End ℂ V) (hE : GlRel E) (hy : IsVec E y)
    (m : Fin (N + 1) → ℂ) (hm : Function.Injective m) (v : V) (hv : v ∈ CapSp E m) :
    ∃ Φ : Fin (N + 1) → Fin (N + 1) → V,
      (∀ x, ∑ i, Φ i x = y x v) ∧
      (∀ i x, Φ i x ∈ CapSp E (Function.update m i (m i - 1))) ∧
      ∀ (i x : Fin (N + 1)) (u : ℂ),
        ∑ l : Fin (N + 1), ((-1 : ℂ) ^ ((x : ℕ) + (l : ℕ))) • qminor (t := N) E (skip1 x) (skip1 l) (u - 1) (Φ i l) =
          (∏ j ∈ Finset.univ.erase i, (u + m j)) • Φ i x := by sorry
