-- Prove2me | solution 1 for iIndepFun_block_extract
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:38:03.692391+00:00
-- url     : https://prove2.me/submissions/6d5ffd84-5844-485a-9a71-c4ce93e4c1d9

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_VCDimension
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Probability.ProductMeasure
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution {X : Type*} [MeasurableSpace X]
    (k m : ℕ) (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D] :
    ProbabilityTheory.iIndepFun (β := fun _ : Fin k => Fin m → X)
      (fun (j : Fin k) (ω : Fin (k * m) → X) => blockExtract k m ω j)
      (MeasureTheory.Measure.pi (fun _ : Fin (k * m) => D)) := by
  open MeasureTheory MeasureTheory.Measure ProbabilityTheory Equiv in
  -- The currying MeasurableEquiv: Fin(k*m) → X  ≃ᵐ  Fin k → (Fin m → X)
  set pcl := MeasurableEquiv.piCongrLeft (fun _ : Fin k × Fin m => X) finProdFinEquiv.symm
  set cur := MeasurableEquiv.curry (Fin k) (Fin m) X
  set e : (Fin (k * m) → X) ≃ᵐ (Fin k → Fin m → X) := pcl.trans cur
  -- blockExtract = e pointwise
  have he : ∀ j ω, blockExtract k m ω j = e ω j := by
    intro j ω; ext i
    simp only [blockExtract, e, MeasurableEquiv.trans_apply, pcl, cur]
    simp [MeasurableEquiv.piCongrLeft, piCongrLeft_apply, MeasurableEquiv.curry,
      Function.curry]
  -- Rewrite goal to use e
  simp_rw [he]
  -- Now goal: iIndepFun (fun j ω => e ω j) (Measure.pi (fun _ => D))
  -- Apply the map characterization
  set μ := Measure.pi (fun _ : Fin (k * m) => D)
  -- AEMeasurable: each component is measurable
  have hmeas : ∀ j : Fin k, AEMeasurable (fun ω => e ω j) μ :=
    fun j => ((measurable_pi_apply j).comp e.measurable).aemeasurable
  rw [iIndepFun_iff_map_fun_eq_pi_map hmeas]
  -- Goal: μ.map (fun ω j => e ω j) = Measure.pi (fun j => μ.map (fun ω => e ω j))
  -- LHS: μ.map (fun ω j => e ω j) = μ.map e
  have hlhs : (fun (ω : Fin (k * m) → X) (j : Fin k) => e ω j) = e := by
    ext ω j; rfl
  rw [hlhs]
  -- Define the nested product measure
  set D' : Fin k → Measure (Fin m → X) := fun _ => Measure.pi (fun _ : Fin m => D)
  -- Step 1: μ.map pcl preserves measure
  have hpcl : MeasurePreserving pcl μ (Measure.pi (fun _ : Fin k × Fin m => D)) :=
    measurePreserving_piCongrLeft (fun _ : Fin k × Fin m => D) finProdFinEquiv.symm
  -- Step 2: (flat on Fin k × Fin m).map cur = nested product
  have hcur : (Measure.pi (fun _ : Fin k × Fin m => D)).map cur = Measure.pi D' := by
    have h1 : Measure.pi (fun _ : Fin k × Fin m => D) =
        infinitePi (fun _ : Fin k × Fin m => D) :=
      (infinitePi_eq_pi (μ := fun _ : Fin k × Fin m => D)).symm
    rw [h1]
    have h3 : D' = fun _ : Fin k => infinitePi (fun _ : Fin m => D) := by
      funext; exact (infinitePi_eq_pi (μ := fun _ : Fin m => D)).symm
    have h2 : Measure.pi D' = infinitePi D' :=
      (infinitePi_eq_pi (μ := D')).symm
    rw [h2, h3]
    exact infinitePi_map_curry (fun _ : Fin k => fun _ : Fin m => D)
  -- Step 3: μ.map e = Measure.pi D'
  have hmap_e : μ.map e = Measure.pi D' := by
    have : (e : (Fin (k * m) → X) → (Fin k → Fin m → X)) = cur ∘ pcl := rfl
    rw [this, ← map_map cur.measurable pcl.measurable, hpcl.map_eq, hcur]
  rw [hmap_e]
  -- RHS: Measure.pi (fun j => μ.map (fun ω => e ω j))
  -- Each marginal: μ.map (fun ω => e ω j) = D' j
  congr 1
  ext j : 1
  -- μ.map (fun ω => e ω j) = j-th marginal of μ.map e = D' j
  have hcomp : (fun ω => e ω j) = (fun f => f j) ∘ (e : (Fin (k * m) → X) → _) := rfl
  rw [hcomp, ← map_map (measurable_pi_apply j) e.measurable, hmap_e]
  exact ((measurePreserving_eval D' j).map_eq).symm
