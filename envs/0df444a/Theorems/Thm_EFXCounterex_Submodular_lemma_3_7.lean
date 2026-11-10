-- Prove2me | Theorems.Thm_EFXCounterex_Submodular_lemma_3_7
-- name    : EFXCounterex.Submodular.lemma_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:45:46.956655+00:00
-- url     : https://prove2.me/theorems/e61e32d6-4072-4a02-9bb4-ba79a399c281
-- title:
--   Lemma 3.7 — ordinal weighted-coverage representation of a set function strictly increasing under inclusion, compatible with relabelling goods
-- statement:
--   For every finite set of goods `Fin m` there is a construction $\Phi$, sending set functions to set functions, such that for every $v$ strictly increasing under inclusion: $\Phi v$ is normalized, $\Phi v$ is a weighted-coverage valuation, $\Phi v(S)\le\Phi v(T)\iff v(S)\le v(T)$ for all bundles $S,T$, and for every permutation $\pi$ of the goods, applying $\Phi$ to the relabelled function $S\mapsto v(\pi(S))$ gives the relabelled result $S\mapsto \Phi v(\pi(S))$.
--
--   Differences from the source:
--   - encoding: a finite set M → Fin m for any m : ℕ (m = 0 included); reason: every finite set is in bijection with some Fin m
--   - generalization: v strictly increasing under inclusion, with the standing §2 conventions of normalization and values in R≥0 → v : Finset (Fin m) → ℝ strictly increasing under inclusion, with no sign or normalization condition; reason: subtracting v(∅) gives a normalized nonnegative strictly increasing function with the same bundle ordering and commutes with relabelling; the source instances are included
--   - reading: "Relabelling goods before applying the construction gives the same result as relabelling them afterwards" → one map Φ for all v with Φ (fun S => v (π(S))) = fun S => Φ v (π(S)) for every strictly increasing v and every permutation π of Fin m (bundles relabelled by image); reason: the clause speaks of 'the construction', so the construction is a single map Φ, and the clause is its equivariance
-- source:
--   Akrami, Mackenzie, Mayorov, Mehlhorn, Srinivas, Suzuki, Weidenbach 2026, Counterexamples to EFX for Submodular and Subadditive Valuations, arXiv:2605.06451 (supplied manuscript, sha256 700243a1…), Lemma 3.7, p. 14

import Mathlib
import Definitions.Def_EFXCounterex_Submodular_Setting

namespace EFXCounterex.Submodular

/-- Lemma 3.7 (ordinal weighted-coverage representation, p. 14). There is a construction `Φ`
sending each set function on the finite set of goods `Fin m` to a set function, such that for
every `v` strictly increasing under inclusion, `Φ v` is a normalized weighted-coverage valuation
with `Φ v S ≤ Φ v T ↔ v S ≤ v T` for all bundles `S, T`; and relabelling the goods by any
permutation `π` before applying the construction gives the same result as relabelling them
afterwards. -/
theorem lemma_3_7 (m : ℕ) :
    ∃ Φ : (Finset (Fin m) → ℝ) → (Finset (Fin m) → ℝ),
      ∀ v : Finset (Fin m) → ℝ, IsStrictlyIncreasing v →
        IsNormalized (Φ v) ∧ IsWeightedCoverage (Φ v) ∧
        (∀ S T : Finset (Fin m), Φ v S ≤ Φ v T ↔ v S ≤ v T) ∧
        ∀ π : Equiv.Perm (Fin m),
          Φ (fun S => v (relabelBundle π S)) = fun S => Φ v (relabelBundle π S) := by sorry

end EFXCounterex.Submodular
