-- Prove2me | solution 1 for mme_stothers_phi125_cyclic_affine_hash_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:29:25.481536+00:00
-- url     : https://prove2.me/submissions/0d3fb6c9-9dbb-4a71-8823-6242ff1f6864

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi125_cyclic_hash_data

open BigOperators
open MME.StothersFourth.Phi125

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p N alpha beta gamma : ℕ}
    (w : Fin 3 → Fin (2 * N) → ZMod p)
    (shift offset : ZMod p) (i : Fin 3)
    (e : CyclicExactEdge N alpha beta gamma) :
    cyclicAffineHash p N alpha beta gamma w shift offset i e =
      shift + (![0, 12 * offset, 6 * offset] : Fin 3 → ZMod p) i +
        ∑ r : Fin 3, ∑ j : Fin (2 * N),
          cyclicHashModeCode p N i (cyclicModeWord e i) r j * w r j := by
  have hsumMul (f : Fin (2 * N) → ZMod p) (c : ZMod p) :
      (∑ j, f j) * c = ∑ j, f j * c := by
    simpa using
      (Finset.sum_mul (Finset.univ : Finset (Fin (2 * N))) f c)
  have hscale2 (u : Fin (2 * N) → Fin 5)
      (v : Fin (2 * N) → ZMod p) :
      (∑ j, ((u j).val : ZMod p) * v j * 2) * 2 =
        ∑ j, ((u j).val : ZMod p) * v j * 4 := by
    calc
      _ = ∑ j, (((u j).val : ZMod p) * v j * 2) * 2 := hsumMul _ 2
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _hj
        ring
  have hscale4 (u : Fin (2 * N) → Fin 5)
      (v : Fin (2 * N) → ZMod p) :
      (∑ j, (-((u j).val : ZMod p) * v j + v j * 4)) * 4 =
        ∑ j, (-((u j).val : ZMod p) * v j * 4 + v j * 16) := by
    calc
      _ = ∑ j,
          (-((u j).val : ZMod p) * v j + v j * 4) * 4 := hsumMul _ 4
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _hj
        ring
  fin_cases i
  · simp [cyclicAffineHash, cyclicHashModeCode,
      MME.StothersFourth.Phi233.cyclicHashModeCode, cyclicModeWord,
      MME.StothersFourth.Phi233.doubledXHash,
      MME.StothersFourth.Phi233.doubledYHash,
      MME.StothersFourth.Phi233.doubledZHash, Fin.sum_univ_succ]
    ring_nf
    rw [hscale2 (modeWord e.2.2.1 1) (w 2)]
    have hb := hscale4 (modeWord e.2.1.1 2) (w 1)
    simp only [neg_mul] at hb
    rw [hb]
  · simp [cyclicAffineHash, cyclicHashModeCode,
      MME.StothersFourth.Phi233.cyclicHashModeCode, cyclicModeWord,
      MME.StothersFourth.Phi233.doubledXHash,
      MME.StothersFourth.Phi233.doubledYHash,
      MME.StothersFourth.Phi233.doubledZHash, Fin.sum_univ_succ]
    ring_nf
    rw [hscale2 (modeWord e.2.1.1 0) (w 1)]
    have hc := hscale4 (modeWord e.2.2.1 2) (w 2)
    simp only [neg_mul] at hc
    rw [hc]
  · simp [cyclicAffineHash, cyclicHashModeCode,
      MME.StothersFourth.Phi233.cyclicHashModeCode, cyclicModeWord,
      MME.StothersFourth.Phi233.doubledXHash,
      MME.StothersFourth.Phi233.doubledYHash,
      MME.StothersFourth.Phi233.doubledZHash, Fin.sum_univ_succ]
    ring
