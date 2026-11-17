-- Prove2me | solution 1 for taggedCommonLimit_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:13:30.465261+00:00
-- url     : https://prove2.me/submissions/ab6175c9-9118-4535-961b-2b330cdeab26

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic
import Theorems.Thm_exists_partition_mesh_lt
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Pointwise Interval
noncomputable section

private theorem source_taggedCommonLimit_unique {a b : ℝ} {f alpha : ℝ → ℝ} {L₁ L₂ : ℝ}
    (h₁ : TaggedCommonLimit a b f alpha L₁)
    (h₂ : TaggedCommonLimit a b f alpha L₂) :
    L₁ = L₂ := by
  rcases h₁ with ⟨hs₁, hlim₁⟩
  rcases h₂ with ⟨_hs₂, hlim₂⟩
  rcases hs₁ with ⟨hab, _⟩
  refine eq_of_forall_dist_le ?_
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlim₁ (eps / 2) hhalf with ⟨δ₁, hδ₁, H₁⟩
  rcases hlim₂ (eps / 2) hhalf with ⟨δ₂, hδ₂, H₂⟩
  rcases exists_partition_mesh_lt hab (lt_min hδ₁ hδ₂) with ⟨P, hPmesh⟩

  -- Define `tags` to precisely match the size `Fin P.n`
  let tags : Fin P.n → ℝ := fun i => P.pts i.castSucc

  -- `leftTagsInPartition P` provides exactly this proof.
  have htags : tagsInPartition P tags := leftTagsInPartition P

  have hmesh₁ : P.mesh < δ₁ := lt_of_lt_of_le hPmesh (min_le_left δ₁ δ₂)
  have hmesh₂ : P.mesh < δ₂ := lt_of_lt_of_le hPmesh (min_le_right δ₁ δ₂)

  have hP₁ := H₁ P tags htags hmesh₁
  have hP₂ := H₂ P tags htags hmesh₂
  have hdecomp :
      L₁ - L₂ = -(taggedSum P tags f alpha - L₁) +
        (taggedSum P tags f alpha - L₂) := by
    ring
  have hlt : |L₁ - L₂| < eps := by
    calc
      |L₁ - L₂| =
          |-(taggedSum P tags f alpha - L₁) +
            (taggedSum P tags f alpha - L₂)| := by rw [hdecomp]
      _ ≤ |-(taggedSum P tags f alpha - L₁)| +
            |taggedSum P tags f alpha - L₂| := abs_add_le _ _
      _ = |taggedSum P tags f alpha - L₁| +
            |taggedSum P tags f alpha - L₂| := by rw [abs_neg]
      _ < eps := by
        have hsum :
            |taggedSum P tags f alpha - L₁| +
                |taggedSum P tags f alpha - L₂| < eps / 2 + eps / 2 :=
          add_lt_add hP₁ hP₂
        simpa using hsum
  have hdist : dist L₁ L₂ < eps := by
    simpa [Real.dist_eq, abs_sub_comm] using hlt
  exact le_of_lt hdist

/-- Source uniqueness of the tagged Riemann–Stieltjes limit. -/
theorem solution {a b : ℝ} {f alpha : ℝ → ℝ} {L₁ L₂ : ℝ}
    (h₁ : TaggedCommonLimit a b f alpha L₁)
    (h₂ : TaggedCommonLimit a b f alpha L₂) :
    L₁ = L₂ := by
  exact source_taggedCommonLimit_unique h₁ h₂
