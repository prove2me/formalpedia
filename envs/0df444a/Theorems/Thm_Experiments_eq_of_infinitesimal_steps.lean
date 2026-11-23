-- Prove2me | Theorems.Thm_Experiments_eq_of_infinitesimal_steps
-- name    : Experiments.eq_of_infinitesimal_steps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:53:24.616276+00:00
-- url     : https://prove2.me/theorems/0f23b44a-3065-45f7-a112-1d05f223ba0e
-- title:
--   Experiments: eq of infinitesimal steps
-- statement:
--   **Euler's step.** Two continuous semigroups whose infinitesimal steps agree to first order
--   are equal, up to a change of speed. Let `M` take the steps `δ` while `E` takes the steps `η`,
--   infinitesimal along `l`, with `δ / η ≈ a`. If `M δ` and `E η` differ by `η` times an
--   infinitesimal, then `M (s a) = E s`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/NonstandardSemigroup.lean#L85-L135
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/NonstandardSemigroup.lean#L85-L135

import Mathlib
import Definitions.Def_Experiments_NonstandardSemigroup
set_option autoImplicit true
open Filter NormedSpace Set
open scoped Topology
noncomputable section
open Experiments
variable {A : Type*} [NormedRing A]
variable [NormedAlgebra ℝ A]

theorem Experiments.eq_of_infinitesimal_steps (M E : ℝ → A)
    (hM : ContinuousOn M (Ici 0)) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t)
    (hE : ContinuousOn E (Ici 0)) (hE0 : E 0 = 1)
    (hEadd : ∀ s t, 0 ≤ s → 0 ≤ t → E (s + t) = E s * E t)
    {ι : Type*} {l : Filter ι} [l.NeBot] (δ η : ι → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hδη : ∀ n, δ n ≤ η n) (hη : ∀ n, 0 < η n) (hz : Tendsto η l (𝓝 0)) {a : ℝ}
    (ha : Tendsto (fun n => δ n / η n) l (𝓝 a))
    (hstep : Tendsto (fun n => (η n)⁻¹ • (M (δ n) - E (η n))) l (𝓝 0)) {s : ℝ} (hs : 0 ≤ s) :
    M (s * a) = E s := by sorry
