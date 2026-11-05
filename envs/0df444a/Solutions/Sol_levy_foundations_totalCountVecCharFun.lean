-- Prove2me | solution 1 for levy_foundations_totalCountVecCharFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T19:59:15.115376+00:00
-- url     : https://prove2.me/submissions/addac1e5-c443-4d8d-a800-0c993dcb03a5

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_charFunDual_poissonRandomMeasureVec
import Theorems.Thm_levy_foundations_measurablePRMEval
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_levy_foundations_poissonRandomMeasure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex

theorem solution
    {Ω E : Type} {ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] [Fintype ι] [DecidableEq ι]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (A : ι → Set E) (hA : ∀ i, MeasurableSet (A i))
    (hfin : ∀ i, m (A i) < ⊤)
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (L : StrongDual ℝ (ι → ℝ)) :
    charFunDual (μ.map fun ω (i : ι) =>
      (LevyFoundations.poissonRandomMeasure K X ω (A i)).toReal) L =
    ∏ i, Complex.exp
      (↑(m (A i)).toReal *
        (Complex.exp (↑(L (Pi.single i 1)) * Complex.I) - 1)) := by
  classical
  have hsource : ProbabilityTheory.IsPoissonPointFamily K X m μ := by
    refine ⟨hd.measurable_count, hd.measurable_point, ?_, ?_, ?_⟩
    · apply (ProbabilityTheory.iIndepFun_iff_iIndep
        (fun i : ℕ ⊕ ℕ × ℕ => ProbabilityTheory.instMeasurableSpacePointFamilyIndexType E i)
        (ProbabilityTheory.pointFamilyCombined K X) μ).2
      have hind := (ProbabilityTheory.iIndepFun_iff_iIndep
        (fun i : ℕ ⊕ ℕ × ℕ => LevyFoundations.instPointFamilyIndexMeasurable E i)
        (LevyFoundations.pointFamilyCombined K X) μ).1 hd.indep
      have heq : (fun i : ℕ ⊕ ℕ × ℕ =>
          MeasurableSpace.comap (LevyFoundations.pointFamilyCombined K X i)
            (LevyFoundations.instPointFamilyIndexMeasurable E i)) =
          (fun i => MeasurableSpace.comap (ProbabilityTheory.pointFamilyCombined K X i)
            (ProbabilityTheory.instMeasurableSpacePointFamilyIndexType E i)) := by
        funext i
        cases i <;> rfl
      rw [heq] at hind
      exact hind
    · intro k
      simpa only [ProbabilityTheory.prmPiece, LevyFoundations.prmPiece] using hd.law_count k
    · intro k n
      convert hd.law_point k n using 1
      unfold ProbabilityTheory.prmPieceLaw LevyFoundations.prmPieceLaw
      simp only [ProbabilityTheory.prmPiece, LevyFoundations.prmPiece]
      split_ifs with h
      · rfl
      · ext s hs
        first | rfl | simp [Measure.smul_apply]
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let B : Fin (Fintype.card ι) → Set E := fun j => A (e.symm j)
  have hB : ∀ j, MeasurableSet (B j) := fun j => hA _
  have hBfin : ∀ j, m (B j) < ⊤ := fun j => hfin _
  have hBdisj : Pairwise (Function.onFun Disjoint B) := by
    intro i j hij
    exact hdisj (fun h => hij (e.symm.injective h))
  let reindex : (Fin (Fintype.card ι) → ℝ) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (e i))
  let L' : StrongDual ℝ (Fin (Fintype.card ι) → ℝ) := L.comp reindex
  have hchar := ProbabilityTheory.charFunDual_poissonRandomMeasureVec
    hsource hB hBfin hBdisj L'
  have hreindex (v : Fin (Fintype.card ι) → ℝ) :
      reindex v = fun i => v (e i) := by
    funext i
    rfl
  have hsingle (j : Fin (Fintype.card ι)) :
      reindex (Pi.single j (1 : ℝ)) = Pi.single (e.symm j) (1 : ℝ) := by
    rw [hreindex]
    funext i
    by_cases h : i = e.symm j
    · subst i
      simp
    · have he : e i ≠ j := by
        intro hij
        apply h
        calc i = e.symm (e i) := (e.symm_apply_apply i).symm
          _ = e.symm j := congrArg e.symm hij
      simp [h, he]
  have hcoeff (j : Fin (Fintype.card ι)) :
      L' (Pi.single j 1) = L (Pi.single (e.symm j) 1) := by
    change L (reindex (Pi.single j 1)) = L (Pi.single (e.symm j) 1)
    rw [hsingle]
  have hprod : (∏ j : Fin (Fintype.card ι),
      Complex.exp (↑(m (B j)).toReal *
        (Complex.exp (↑(L' (Pi.single j 1)) * Complex.I) - 1))) =
      ∏ i : ι, Complex.exp (↑(m (A i)).toReal *
        (Complex.exp (↑(L (Pi.single i 1)) * Complex.I) - 1)) := by
    apply Fintype.prod_equiv e.symm
    intro j
    simp only [B, hcoeff]
  have mA : Measurable (fun ω (i : ι) =>
      (LevyFoundations.poissonRandomMeasure K X ω (A i)).toReal) :=
    measurable_pi_lambda _ (fun i =>
      (levy_foundations_measurablePRMEval K X hd.measurable_count
        hd.measurable_point (hA i)).ennreal_toReal)
  have mB : Measurable (fun ω (j : Fin (Fintype.card ι)) =>
      (ProbabilityTheory.poissonRandomMeasure K X ω (B j)).toReal) := by
    simpa only [ProbabilityTheory.poissonRandomMeasure,
      LevyFoundations.poissonRandomMeasure] using
      (measurable_pi_lambda _ (fun j =>
        (levy_foundations_measurablePRMEval K X hd.measurable_count
          hd.measurable_point (hB j)).ennreal_toReal))
  have hmap : charFunDual (μ.map fun ω (i : ι) =>
      (LevyFoundations.poissonRandomMeasure K X ω (A i)).toReal) L =
      charFunDual (μ.map fun ω (j : Fin (Fintype.card ι)) =>
        (ProbabilityTheory.poissonRandomMeasure K X ω (B j)).toReal) L' := by
    rw [charFunDual_apply, charFunDual_apply,
      integral_map mA.aemeasurable (by fun_prop),
      integral_map mB.aemeasurable (by fun_prop)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have hw : L (fun i : ι =>
        (LevyFoundations.poissonRandomMeasure K X ω (A i)).toReal) =
        L' (fun j : Fin (Fintype.card ι) =>
          (ProbabilityTheory.poissonRandomMeasure K X ω (B j)).toReal) := by
      change L (fun i => _) = L (reindex (fun j => _))
      congr 1
      rw [hreindex]
      funext i
      simp only [B, ProbabilityTheory.poissonRandomMeasure,
        LevyFoundations.poissonRandomMeasure, e.symm_apply_apply]
    simpa only [hw]
  exact hmap.trans (hchar.trans hprod)
