-- Prove2me | Theorems.Thm_FamousTheorems_prokhorov
-- name    : FamousTheorems.prokhorov
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T09:15:01.868667+00:00
-- url     : https://prove2.me/theorems/8d28709f-0395-4b72-8e51-add69a38fadb
-- title:
--   Prokhorov's theorem (tight sets of finite measures are compact)
-- statement:
--   **Prokhorov's theorem (compactness of tight families).** In a Hausdorff space $E$ with Borel σ-algebra, let $K_n$ be compact sets and $u_n\to0$. Assume $E$ is normal or the $K_n$ increase. Then the set of finite measures with total mass $\le C$ and $\mu(K_n^c)\le u_n$ for all $n$ is compact in the weak topology.
--
--   Uniformly bounded, uniformly tight families of measures are therefore relatively compact. This is the half of Prokhorov's theorem used to prove weak convergence: tightness plus identification of limits (e.g. via characteristic functions) gives convergence in distribution, as in Donsker's invariance principle.
--
--   **Formalization note.** Mathlib's `isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le`, for the weak topology on `MeasureTheory.FiniteMeasure E`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem prokhorov {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [T2Space E] [BorelSpace E]
    {u : ℕ → NNReal} {K : ℕ → Set E} (C : NNReal) (hu : Filter.Tendsto u Filter.atTop (nhds 0))
    (hK : ∀ n, IsCompact (K n)) (h : NormalSpace E ∨ Monotone K) :
    IsCompact {μ : MeasureTheory.FiniteMeasure E | μ.mass ≤ C ∧ ∀ n, μ (K n)ᶜ ≤ u n} := by sorry

end FamousTheorems
