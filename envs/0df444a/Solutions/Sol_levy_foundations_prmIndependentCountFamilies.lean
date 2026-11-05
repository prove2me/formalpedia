-- Prove2me | solution 1 for levy_foundations_prmIndependentCountFamilies
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:53:23.55324+00:00
-- url     : https://prove2.me/submissions/a1b05e2c-9d8f-47db-a2c5-a6fb509c750d

import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_poissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_iIndepFun_poissonRandomMeasure_families

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

theorem solution
    {Ω E : Type} {ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] [Fintype ι] (m : Measure E) [SigmaFinite m]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    {ιB : ι → Type*} [∀ i, Fintype (ιB i)]
    (B : ∀ i, ιB i → Set E)
    (hB : ∀ i b, MeasurableSet (B i b))
    (hfin : ∀ i b, m (B i b) < ⊤)
    (hdisj : ∀ i j, i ≠ j → ∀ b b', Disjoint (B i b) (B j b')) :
    iIndepFun (fun i ω (b : ιB i) =>
      LevyFoundations.poissonRandomMeasure K X ω (B i b)) μ := by
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
  let F : Fin (Fintype.card ι) → Type := fun j => Fin (Fintype.card (ιB (e.symm j)))
  let ef (j : Fin (Fintype.card ι)) : ιB (e.symm j) ≃ F j :=
    Fintype.equivFin (ιB (e.symm j))
  let C : (j : Fin (Fintype.card ι)) → F j → Set E := fun j k => B (e.symm j) ((ef j).symm k)
  have hCm : ∀ j k, MeasurableSet (C j k) := fun j k => hB _ _
  have hCfin : ∀ j k, m (C j k) < ⊤ := fun j k => hfin _ _
  have hCdisj : ∀ j j', j ≠ j' → ∀ k k', Disjoint (C j k) (C j' k') := by
    intro j j' hjj k k'
    exact hdisj (e.symm j) (e.symm j')
      (fun he => hjj (e.symm.injective he)) _ _
  have hcoded : iIndepFun
      (fun j ω (k : F j) => ProbabilityTheory.poissonRandomMeasure K X ω (C j k)) μ :=
    ProbabilityTheory.iIndepFun_poissonRandomMeasure_families
      hsource hCm hCfin hCdisj
  let G : (j : Fin (Fintype.card ι)) →
      (F j → ENNReal) → (ιB (e.symm j) → ENNReal) :=
    fun j f b => f (ef j b)
  have hG : ∀ j, Measurable (G j) :=
    fun j => measurable_pi_lambda _ fun b => measurable_pi_apply (ef j b)
  have hblocks : iIndepFun
      (fun j ω (b : ιB (e.symm j)) =>
        ProbabilityTheory.poissonRandomMeasure K X ω (B (e.symm j) b)) μ := by
    simpa [G, C, F, ef, Function.comp_def] using hcoded.comp G hG
  have hsigma : iIndep
      (fun j : Fin (Fintype.card ι) =>
        MeasurableSpace.comap
          (fun ω (b : ιB (e.symm j)) =>
            ProbabilityTheory.poissonRandomMeasure K X ω (B (e.symm j) b))
          (inferInstance : MeasurableSpace (ιB (e.symm j) → ENNReal))) μ := by
    exact (ProbabilityTheory.iIndepFun_iff_iIndep
      (fun j : Fin (Fintype.card ι) =>
        (inferInstance : MeasurableSpace (ιB (e.symm j) → ENNReal)))
      (fun j ω (b : ιB (e.symm j)) =>
        ProbabilityTheory.poissonRandomMeasure K X ω (B (e.symm j) b)) μ).1 hblocks
  have hreindex := hsigma.precomp e.injective
  apply (ProbabilityTheory.iIndepFun_iff_iIndep
    (fun i : ι => (inferInstance : MeasurableSpace (ιB i → ENNReal)))
    (fun i ω (b : ιB i) =>
      ProbabilityTheory.poissonRandomMeasure K X ω (B i b)) μ).2
  have hfamily_eq :
      (fun i : ι =>
        MeasurableSpace.comap
          (fun ω (b : ιB (e.symm (e i))) =>
            ProbabilityTheory.poissonRandomMeasure K X ω (B (e.symm (e i)) b))
          (inferInstance : MeasurableSpace (ιB (e.symm (e i)) → ENNReal))) =
      (fun i : ι =>
        MeasurableSpace.comap
          (fun ω (b : ιB i) =>
            ProbabilityTheory.poissonRandomMeasure K X ω (B i b))
          (inferInstance : MeasurableSpace (ιB i → ENNReal))) := by
    funext i
    have hi : e.symm (e i) = i := e.symm_apply_apply i
    rw [hi]
  change iIndep
      (fun i : ι =>
        MeasurableSpace.comap
          (fun ω (b : ιB (e.symm (e i))) =>
            ProbabilityTheory.poissonRandomMeasure K X ω (B (e.symm (e i)) b))
          (inferInstance : MeasurableSpace (ιB (e.symm (e i)) → ENNReal))) μ at hreindex
  rw [hfamily_eq] at hreindex
  exact hreindex
