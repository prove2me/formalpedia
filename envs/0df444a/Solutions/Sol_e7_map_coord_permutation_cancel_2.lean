-- Prove2me | solution 2 for e7_map_coord_permutation_cancel
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T08:19:20.05959+00:00
-- url     : https://prove2.me/submissions/587c7013-260d-4a91-9ac1-65f14524081e

import Mathlib

open MeasureTheory

theorem solution {ι E Ω Ω' : Type*} [MeasurableSpace E]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω')
    (x : Ω → ι → E) (y : Ω' → ι → E)
    (σ : Equiv.Perm ι) (hx : Measurable x) (hy : Measurable y)
    (hperm : Measure.map (fun ω i => x ω (σ i)) P =
      Measure.map (fun ω i => y ω (σ i)) Q) :
    Measure.map x P = Measure.map y Q := by
  let τ : (ι → E) → (ι → E) := fun z i => z (σ i)
  let τinv : (ι → E) → (ι → E) := fun z i => z (σ.symm i)
  have hτ : Measurable τ := by
    rw [measurable_pi_iff]
    intro i
    exact measurable_pi_apply (σ i)
  have hτinv : Measurable τinv := by
    rw [measurable_pi_iff]
    intro i
    exact measurable_pi_apply (σ.symm i)
  have hperm' : Measure.map τ (Measure.map x P) = Measure.map τ (Measure.map y Q) := by
    rw [Measure.map_map hτ hx, Measure.map_map hτ hy]
    exact hperm
  have hid : τinv ∘ τ = id := by
    funext z i
    simp [τ, τinv]
  have h := congrArg (Measure.map τinv) hperm'
  have hL : Measure.map τinv (Measure.map τ (Measure.map x P)) = Measure.map x P := by
    rw [Measure.map_map hτinv hτ, hid, Measure.map_id]
  have hR : Measure.map τinv (Measure.map τ (Measure.map y Q)) = Measure.map y Q := by
    rw [Measure.map_map hτinv hτ, hid, Measure.map_id]
  rw [hL, hR] at h
  exact h
