-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_BB_eq_sum
-- name    : Formalism.FourierDecayAlt.P.A5x4.BB_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:58.067839+00:00
-- url     : https://prove2.me/theorems/b5a67eb6-b94c-41cb-98d9-5b354f5dd550
-- title:
--   A5x4: BB eq sum
-- statement:
--   The A5x4 construction uses the BB eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelQuotientFinite.lean#L173-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelQuotientFinite.lean#L173-L209

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
open Classical

theorem Formalism.FourierDecayAlt.P.A5x4.BB_eq_sum {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    (R : Subring K) (ψ : AddChar K ℂ) (hL : LocalDatum K R ψ) (w : Point K)
    (μ₁ : Measure (lowW K w.1 w.2)) (μ₂ : Measure (upUniG K w.1.sum))
    [μ₁.IsMulRightInvariant] [μ₂.IsMulLeftInvariant] [SFinite μ₁] [SFinite μ₂]
    (h1 : μ₁ (intSub R (lowW K w.1 w.2) : Set (lowW K w.1 w.2)) = 1)
    (h2 : μ₂ (intSub R (upUniG K w.1.sum) : Set (upUniG K w.1.sum)) = 1)
    (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R)
    (h : {q : Cos R w | IsInt R (orbZ w (rep R q))}.Finite) :
    BB R w.1 w.2 ψ C e lam μ₁ μ₂ = ∑ q ∈ h.toFinset,
      (Nat.card (isoSet R (orbZ w (rep R q)) C e lam) : ℂ) * phase ψ (rep R q) := by sorry
