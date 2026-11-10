-- Prove2me | Theorems.Thm_EFXCounterex_Submodular_strictification
-- name    : EFXCounterex.Submodular.strictification
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:45:39.045194+00:00
-- url     : https://prove2.me/theorems/de92f181-bd92-4ce5-bf63-b3e82ce583d2
-- title:
--   §3.2.2 strictification — $v^\varepsilon_i(S)=v_i(S)+\varepsilon|S|$ is strictly increasing, keeps strict comparisons and symmetries, and EFX for $v^\varepsilon$ implies EFX for $v$
-- statement:
--   Let $v$ be a profile of normalized monotone valuations of $n$ agents over $m$ goods. There is $\varepsilon_0>0$ such that for every common $\varepsilon\in(0,\varepsilon_0)$ the perturbed profile $v^\varepsilon_i(S)=v_i(S)+\varepsilon|S|$ satisfies: (i) every $v^\varepsilon_i$ is normalized; (ii) every $v^\varepsilon_i$ is strictly increasing under inclusion; (iii) every strict comparison is preserved: $v_i(S)<v_j(T)$ implies $v^\varepsilon_i(S)<v^\varepsilon_j(T)$; (iv) every allocation that is EFX for $v^\varepsilon$ is EFX for $v$; (v) every simultaneous relabelling $(\sigma,\pi)$ of agents and goods that is a symmetry of $v$ is a symmetry of $v^\varepsilon$.
--
--   Differences from the source:
--   - encoding: valuations v_i : 2^M → R≥0, normalized and monotone → v : Fin n → Finset (Fin m) → ℝ with IsNormalized (v i) and IsMonotone (v i); reason: a normalized monotone real set function is nonnegative, so the instances are the same
--   - encoding: an allocation is a tuple of pairwise disjoint bundles whose union is M (empty bundles allowed, no unallocated goods) → X : Fin n → Finset (Fin m) with IsAllocation X := LittleCharity.EFX.IsPartialAllocation X ∧ LittleCharity.EFX.pool X = ∅; reason: pairwise disjoint plus empty pool (no unallocated good) is exactly 'union is M'
--   - reading: "For a sufficiently small common ε > 0" → ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ → …; reason: the standard meaning of 'sufficiently small'
--   - reading: the paragraph's profile v (any valuations on the agents N and goods M) → any n, m and any normalized monotone profile v : Fin n → Finset (Fin m) → ℝ; reason: §3.2.2 states the step for an arbitrary monotone profile; p. 14: 'The two steps transfer every monotone EFX counterexample'
--   - reading: "preserve every original strict comparison" → ∀ i j S T, v i S < v j T → perturb ε v i S < perturb ε v j T; reason: the stronger reading, which also covers comparisons between two agents' values; the per-agent comparisons are the case i = j
--   - encoding: "every symmetry of the original profile under simultaneous relabeling of agents and goods" → every σ : Equiv.Perm (Fin n), π : Equiv.Perm (Fin m) with IsProfileSymmetry v σ π (v (σ i) (π(S)) = v i S for all i, S); reason: a symmetry is a relabelling that leaves the profile unchanged
-- source:
--   Akrami, Mackenzie, Mayorov, Mehlhorn, Srinivas, Suzuki, Weidenbach 2026, Counterexamples to EFX for Submodular and Subadditive Valuations, arXiv:2605.06451 (supplied manuscript, sha256 700243a1…), §3.2.2, display v^ε_i(S) = v_i(S) + ε|S| and the paragraph after it, pp. 13–14

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting
import Definitions.Def_EFXCounterex_Submodular_Setting

namespace EFXCounterex.Submodular

/-- §3.2.2 (pp. 13–14), strictification. For any profile of normalized monotone valuations on `n`
agents and `m` goods, there is `ε₀ > 0` such that for every common `ε ∈ (0, ε₀)` the perturbed
profile `v^ε_i(S) = v_i(S) + ε|S|` is normalized and strictly increasing under inclusion, preserves
every strict comparison `v_i(S) < v_j(T)` of the original profile (for the same agent or two
agents), every EFX allocation for `v^ε` is EFX for `v`, and
every symmetry of `v` under a simultaneous relabelling of agents and goods is a symmetry of
`v^ε`. -/
theorem strictification {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (∀ i, IsNormalized (perturb ε v i)) ∧
      (∀ i, IsStrictlyIncreasing (perturb ε v i)) ∧
      (∀ i j S T, v i S < v j T → perturb ε v i S < perturb ε v j T) ∧
      (∀ X : Fin n → Finset (Fin m), IsAllocation X →
        LittleCharity.EFX.IsEFX (perturb ε v) X → LittleCharity.EFX.IsEFX v X) ∧
      (∀ (σ : Equiv.Perm (Fin n)) (π : Equiv.Perm (Fin m)),
        IsProfileSymmetry v σ π → IsProfileSymmetry (perturb ε v) σ π) := by sorry

end EFXCounterex.Submodular
