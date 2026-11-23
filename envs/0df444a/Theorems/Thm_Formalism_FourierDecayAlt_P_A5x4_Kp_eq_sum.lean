-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_Kp_eq_sum
-- name    : Formalism.FourierDecayAlt.P.A5x4.Kp_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:26:06.072887+00:00
-- url     : https://prove2.me/theorems/079b601b-4845-4244-b3d7-6a70f62fa5b7
-- title:
--   A5x4: Kp eq sum
-- statement:
--   The A5x4 construction uses the Kp eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelQuotientFinite.lean#L148-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelQuotientFinite.lean#L148-L169

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x4

theorem Formalism.FourierDecayAlt.P.A5x4.Kp_eq_sum {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (w w' : Point K)
    (h : {q : Cos R w | IsInt R (orbZ w (rep R q))}.Finite)
    (h' : {q : Cos R w' | IsInt R (orbZ w' (rep R q))}.Finite) :
    Kp R ψ w w' = ∑ q ∈ h.toFinset, ∑ q' ∈ h'.toFinset,
      (Nat.card (isoZZ R (orbZ w (rep R q)) (orbZ w' (rep R q'))) : ℂ) * phase ψ (rep R q) *
        conj (phase ψ (rep R q')) := by sorry
