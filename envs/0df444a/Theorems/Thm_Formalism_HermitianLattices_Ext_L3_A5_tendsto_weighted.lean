-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_tendsto_weighted
-- name    : Formalism.HermitianLattices.Ext.L3.A5.tendsto_weighted
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:50.994644+00:00
-- url     : https://prove2.me/theorems/28d91297-6f1f-4350-8d0c-4b37e301a385
-- title:
--   A5: tendsto weighted
-- statement:
--   The A5 construction uses the tendsto weighted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoWeightedTprod.lean#L61-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoWeightedTprod.lean#L61-L105

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoWeightedTprod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.A5
variable {ι X : Type*} {q : ι → ℝ}
open scoped Classical

theorem Formalism.HermitianLattices.Ext.L3.A5.tendsto_weighted (hq : ∀ i, 2 ≤ q i) (hsum : Summable fun i => (q i ^ 2)⁻¹)
    (S : Finset ι) {R : ι → ℕ → ℝ} (hR0 : ∀ i, R i 0 = 1) (hRS : ∀ i ∈ S, ∀ j, R i j = 1)
    (hRb : ∀ i j, |R i (j + 1) - R i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i)
    (val : X → ι →₀ ℕ) (B : ℕ → Finset X) (a : X → ℝ) (sc : ℕ → ℝ) (c C : ℝ)
    (H1 : ∀ v : ι →₀ ℕ, Disjoint v.support S →
      Tendsto (fun j => sc j * ∑ n ∈ (B j).filter (fun n => v ≤ val n), a n) atTop
        (𝓝 (c / nrm q v)))
    (H2 : ∀ᶠ j in atTop, ∀ v : ι →₀ ℕ,
      |sc j * ∑ n ∈ (B j).filter (fun n => v ≤ val n), a n| ≤ C / nrm q v) :
    Tendsto (fun j => sc j * ∑ n ∈ B j, a n * (val n).prod R) atTop
      (𝓝 (c * ∑' v : ι →₀ ℕ, v.prod (dif R) / nrm q v)) := by sorry
