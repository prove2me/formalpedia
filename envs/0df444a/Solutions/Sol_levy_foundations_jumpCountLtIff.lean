-- Prove2me | solution 1 for levy_foundations_jumpCountLtIff
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T00:27:56.209206+00:00
-- url     : https://prove2.me/submissions/a7fb0848-baa9-4a96-b0e6-a82beaca930d

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_piecewisePath
open Filter Set Topology

theorem solution
    (T : ℕ → ℝ) (hmono : StrictMono T) (htop : Tendsto T atTop atTop)
    (n : ℕ) (t : ℝ) :
    n < LevyFoundations.jumpCount T t ↔ T n ≤ t := by
  have hne : {m | t < T m}.Nonempty := by
    obtain ⟨m, hm⟩ := (htop.eventually_gt_atTop t).exists
    exact ⟨m, hm⟩
  unfold LevyFoundations.jumpCount
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    exact absurd (Nat.sInf_le (show n ∈ {m | t < T m} from hlt)) (not_le.mpr h)
  · intro h
    by_contra hle
    push_neg at hle
    have hm : sInf {m | t < T m} ∈ {m | t < T m} := Nat.sInf_mem hne
    have h1 : T (sInf {m | t < T m}) ≤ T n := hmono.monotone hle
    have hm' : t < T (sInf {m | t < T m}) := hm
    linarith

