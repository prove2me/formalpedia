-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_euler_identity
-- name    : Formalism.HermitianLattices.Ext.L3.A5.euler_identity
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:59.146848+00:00
-- url     : https://prove2.me/theorems/a46975b6-4013-4e73-934c-1480bb967432
-- title:
--   A5: euler identity
-- statement:
--   The A5 construction uses the euler identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoWeightedTprod.lean#L144-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoWeightedTprod.lean#L144-L211

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

theorem Formalism.HermitianLattices.Ext.L3.A5.euler_identity (hq : ∀ i, 2 ≤ q i) (hsum : Summable fun i => (q i ^ 2)⁻¹)
    (S : Finset ι) {ρ : ι → ℕ → ℝ} (hρ0 : ∀ i, ρ i 0 = 1) (hρS : ∀ i ∈ S, ∀ j, ρ i j = 1)
    (hρb : ∀ i j, |ρ i (j + 1) - ρ i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i)
    (val : X → ι →₀ ℕ) (B : ℕ → Finset X) (a : X → ℝ) (sc : ℕ → ℝ) (c c0 C : ℝ) (E : ι → ℝ)
    (hc : c0 = 0 → c = 0)
    (H1 : ∀ v : ι →₀ ℕ, Disjoint v.support S →
      Tendsto (fun j => sc j * ∑ n ∈ (B j).filter (fun n => v ≤ val n), a n) atTop
        (𝓝 (c / nrm q v)))
    (H2 : ∀ᶠ j in atTop, ∀ v : ι →₀ ℕ,
      |sc j * ∑ n ∈ (B j).filter (fun n => v ≤ val n), a n| ≤ C / nrm q v)
    (H3 : ∀ S' : Finset ι, S ⊆ S' →
      Tendsto (fun j => sc j * ∑ n ∈ B j, a n * ∏ i ∈ S', ρ i (val n i)) atTop
        (𝓝 (c0 * ∏ i ∈ S', E i))) :
    c * ∑' v : ι →₀ ℕ, v.prod (dif ρ) / nrm q v = c0 * ∏' i, E i := by sorry
