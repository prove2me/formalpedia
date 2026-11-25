-- Prove2me | Theorems.Thm_CompanionTheory_Bmu_CWLin_eq_zero
-- name    : CompanionTheory.Bmu.CWLin.eq_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:17:16.272133+00:00
-- url     : https://prove2.me/theorems/8ed3f596-adb9-4a5e-b83f-55c6d356190e
-- title:
--   CWLin: eq zero
-- statement:
--   The CWLin construction uses the eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselOrbitBounds/BesselMapUniqueness/ContinuousOnOrbit.lean#L78-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselOrbitBounds/BesselMapUniqueness/ContinuousOnOrbit.lean#L78-L98

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_ContinuousOnOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
open scoped ContDiff InnerProductSpace ComplexConjugate
noncomputable section
open CompanionTheory CompanionTheory.Bmu
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {Hm : Mat n} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mat n → (H →L[ℂ] H)} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
omit [CompleteSpace H]

theorem CompanionTheory.Bmu.CWLin.eq_zero (hU : URep Hm σ) {B : H → V} (hB : CWLin Hm σ B) {w : H} (hw : IsSm (UH Hm) σ w)
    (h0 : ∀ g ∈ UH Hm, B (σ g w) = 0) {x : H} (hx : IsSm (UH Hm) σ x)
    (happ : ∀ Ws : List (List (Mat n)), (∀ W ∈ Ws, LieWd Hm W) → ∀ δ : ℝ, 0 < δ →
      ∃ (N : ℕ) (c : Fin N → ℂ) (g : Fin N → Mat n), (∀ i, g i ∈ UH Hm) ∧
        (Ws.map fun W => ‖dsW σ W (x - ∑ i, c i • σ (g i) w)‖).sum < δ) : B x = 0 := by sorry
