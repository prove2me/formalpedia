-- Prove2me | solution 1 for levy_foundations_smallJumpIntegralLpIncrement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:01:21.950067+00:00
-- url     : https://prove2.me/submissions/f8586b56-0a42-45c8-82e7-eb97134b6bc9

import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_levy_foundations_smallJumpIntegralLp
import Definitions.Def_levy_foundations_isCompensatedPoissonL2Extension
import Theorems.Thm_levy_foundations_smallJumpBandMemLpTwo

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (ν : Measure ℝ)
    [SigmaFinite ν] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → ℝ × ℝ)
    (I : Lp ℝ 2 (volume.prod ν) → Lp ℝ 2 μ)
    (hI : LevyFoundations.IsCompensatedPoissonL2Extension
      (volume.prod ν) μ K X I)
    (hν : LevyFoundations.isLevyMeasure ν)
    (s t : ℝ) (h0 : 0 ≤ s) (hst : s ≤ t) :
    LevyFoundations.smallJumpIntegralLp ν μ I hν t -
      LevyFoundations.smallJumpIntegralLp ν μ I hν s =
    I (by
      classical
      let f : ℝ × ℝ → ℝ :=
        (Set.Ioc s t ×ˢ Set.Ioo (-1 : ℝ) 1).indicator (fun p => p.2)
      exact if h : MemLp f 2 (volume.prod ν) then h.toLp f else 0) := by
  classical
  let f (a b : ℝ) : ℝ × ℝ → ℝ :=
    (Set.Ioc a b ×ˢ Set.Ioo (-1 : ℝ) 1).indicator (fun p => p.2)
  have hm (a b : ℝ) : MemLp (f a b) 2 (volume.prod ν) :=
    levy_foundations_smallJumpBandMemLpTwo ν hν a b
  have hset :
      Set.Ioc 0 t ×ˢ Set.Ioo (-1 : ℝ) 1 =
        (Set.Ioc 0 s ×ˢ Set.Ioo (-1 : ℝ) 1) ∪
          (Set.Ioc s t ×ˢ Set.Ioo (-1 : ℝ) 1) := by
    ext p
    simp only [Set.mem_prod, Set.mem_union, Set.mem_Ioc]
    constructor
    · rintro ⟨⟨hp0, hpt⟩, hpj⟩
      by_cases hps : p.1 ≤ s
      · exact Or.inl ⟨⟨hp0, hps⟩, hpj⟩
      · exact Or.inr ⟨⟨lt_of_not_ge hps, hpt⟩, hpj⟩
    · rintro (h | h)
      · exact ⟨⟨h.1.1, le_trans h.1.2 hst⟩, h.2⟩
      · exact ⟨⟨lt_of_le_of_lt h0 h.1.1, h.1.2⟩, h.2⟩
  have hdisj : Disjoint
      (Set.Ioc 0 s ×ˢ Set.Ioo (-1 : ℝ) 1)
      (Set.Ioc s t ×ˢ Set.Ioo (-1 : ℝ) 1) := by
    apply Set.disjoint_left.mpr
    intro p hp1 hp2
    exact (not_lt_of_ge hp1.1.2) hp2.1.1
  have hpoint (p : ℝ × ℝ) : f 0 t p = f 0 s p + f s t p := by
    dsimp only [f]
    rw [hset, Set.indicator_union_of_disjoint hdisj]
  have hLp : (hm 0 t).toLp (f 0 t) =
      (hm 0 s).toLp (f 0 s) + (hm s t).toLp (f s t) := by
    apply Lp.ext
    filter_upwards [(hm 0 t).coeFn_toLp, (hm 0 s).coeFn_toLp,
      (hm s t).coeFn_toLp,
      Lp.coeFn_add ((hm 0 s).toLp (f 0 s)) ((hm s t).toLp (f s t))]
      with p h0t h0s hstp hsum
    simpa only [hsum, h0t, h0s, hstp, Pi.add_apply] using hpoint p
  change I (if h : MemLp (f 0 t) 2 (volume.prod ν) then h.toLp (f 0 t) else 0) -
      I (if h : MemLp (f 0 s) 2 (volume.prod ν) then h.toLp (f 0 s) else 0) =
    I (if h : MemLp (f s t) 2 (volume.prod ν) then h.toLp (f s t) else 0)
  rw [dif_pos (hm 0 t), dif_pos (hm 0 s), dif_pos (hm s t), hLp, hI.map_add]
  abel