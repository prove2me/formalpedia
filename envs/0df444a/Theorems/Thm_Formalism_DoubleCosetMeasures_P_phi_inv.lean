-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_phi_inv
-- name    : Formalism.DoubleCosetMeasures.P.phi_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:39.834556+00:00
-- url     : https://prove2.me/theorems/d3a81215-57dc-4ef0-b9dd-7777a35f95b3
-- title:
--   P: phi inv
-- statement:
--   The P construction uses the phi inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsOpenIsIntSet.lean#L53-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsOpenIsIntSet.lean#L53-L92

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures

theorem Formalism.DoubleCosetMeasures.P.phi_inv (hIntInv : IntInv) (hIsoInv : IsoInv) (hSA : SimpleAdd)
    {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (s : List ℕ) (t : ℕ → Kˣ) (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1)
    (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R) :
    ∀ a ∈ intSub R (lowW K s t), ∀ b ∈ intSub R (upUniG K s.sum), ∀ x : lowW K s t,
      ∀ y : upUniG K s.sum, phi R s t ψ C e lam (a * x, y * b) = phi R s t ψ C e lam (x, y) := by sorry
