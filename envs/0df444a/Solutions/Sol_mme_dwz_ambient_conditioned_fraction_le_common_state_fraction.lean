-- Prove2me | solution 1 for mme_dwz_ambient_conditioned_fraction_le_common_state_fraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T03:25:51.606858+00:00
-- url     : https://prove2.me/submissions/a9fc787f-1fee-45e8-99af-4f57e0cad5f6

import Definitions.Def_mme_dwz_global_common_state_broken_copy
import Definitions.Def_mme_dwz_global_ambient_conditioned_broken_copy
import Theorems.Thm_mme_dwz_table2_affine_hash_bucket_mem_iff_retains
import Theorems.Thm_mme_dwz_ambient_conditioned_nonholes_le_common_state_selected

open MME

set_option autoImplicit false
set_option warningAsError true

/-!
# Normalized ambient mass survives selected-family restriction

This is the exact termwise form needed after weighted enumeration.  Canonical
bucket membership supplies affine retention at the common state, the proved
cardinality transport compares nonholes, and division by the common useful-
block cardinal preserves the inequality.
-/

theorem solution
    (m : ℕ) {p N L k : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (reindex : Fin (N + 1) ≃ Fin L)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A : Finset (Fin (N + 1) → Fin 15))
    (Tnative : Finset (Fin L → Fin 15))
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin k → Fin (N + 1) → Fin 15)
    (hedgeT : ∀ j,
      MME.DWZGlobalCorrelated.sourceWord reindex edge j ∈ Tnative)
    (hedgeInjective : Function.Injective edge)
    (r : Fin k)
    (hedgeBucket : edge r ∈ MME.dwzTable2AffineHashBucket S A q) :
    let retained := MME.DWZGlobalCorrelated.sourceWord reindex edge r
    (((MME.DWZGlobalCorrelated.ambientConditionedBrokenCopy
          m reindex Tnative retained (hedgeT r)
            (fun t ↦ q.1 t.castSucc)).nonholes.card : ℕ) : ℝ) /
        (Fintype.card
          (MME.DWZTable2StandardForm.UsefulBlock m retained) : ℝ) ≤
      MME.DWZSquare.nonholeFraction
        (MME.DWZGlobalCorrelated.commonStateBrokenCopy
          m reindex q edge r) := by
  dsimp only
  let retained := MME.DWZGlobalCorrelated.sourceWord reindex edge r
  have hedgeA : edge r ∈ A := by
    exact (Finset.mem_filter.mp hedgeBucket).1
  have hretains : MME.dwzAsymmetricAffineRetains (4 : ZMod p)
      (S.image (fun x : ℕ ↦ (x : ZMod p)))
      (MME.dwzTable2CastX (edge r))
      (MME.dwzTable2CastY (edge r))
      (MME.dwzTable2CastZ (edge r)) q :=
    (mme_dwz_table2_affine_hash_bucket_mem_iff_retains
      hpodd S hSrange hSfree A (edge r) hedgeA q).mp hedgeBucket
  have hcard := mme_dwz_ambient_conditioned_nonholes_le_common_state_selected
    m hpodd reindex (S.image (fun x : ℕ ↦ (x : ZMod p))) Tnative q
      edge hedgeT hedgeInjective r hretains
  have hcardReal :
      (((MME.DWZGlobalCorrelated.ambientConditionedBrokenCopy
          m reindex Tnative retained (hedgeT r)
            (fun t ↦ q.1 t.castSucc)).nonholes.card : ℕ) : ℝ) ≤
        (((MME.DWZGlobalCorrelated.commonStateBrokenCopy
          m reindex q edge r).nonholes.card : ℕ) : ℝ) := by
    exact_mod_cast hcard
  simpa only [MME.DWZSquare.nonholeFraction] using
    (div_le_div_of_nonneg_right hcardReal
      (Nat.cast_nonneg (Fintype.card
        (MME.DWZTable2StandardForm.UsefulBlock m retained)) :
          0 ≤ (Fintype.card
            (MME.DWZTable2StandardForm.UsefulBlock m retained) : ℝ)))
