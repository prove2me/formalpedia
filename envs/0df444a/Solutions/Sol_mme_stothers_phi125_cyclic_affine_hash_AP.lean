-- Prove2me | solution 1 for mme_stothers_phi125_cyclic_affine_hash_AP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:22:02.607725+00:00
-- url     : https://prove2.me/submissions/5ee680f0-3a8f-4b43-a573-4f73656b2846

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi125_cyclic_hash_data

open BigOperators
open MME.StothersFourth.Phi125

set_option autoImplicit false
set_option warningAsError true

private theorem basic_doubled_hash_AP
    {R : Type} [CommRing R] {N alpha beta gamma : ℕ}
    (b : R) (w : Fin (2 * N) → R)
    (x y z : ExactProfileWord N alpha beta gamma)
    (hsupp : CoordinatewiseSupported x y z) :
    MME.StothersFourth.Phi233.doubledXHash (R := R) (N := N)
        b w (modeWord x.1 0) +
      MME.StothersFourth.Phi233.doubledYHash (R := R) (N := N)
        b w (modeWord y.1 1) =
      (2 : R) * MME.StothersFourth.Phi233.doubledZHash
        (R := R) (N := N) b w (modeWord z.1 2) := by
  have hsum (j : Fin (2 * N)) :
      (modeWord x.1 0 j).val + (modeWord y.1 1 j).val +
          (modeWord z.1 2 j).val = 4 := by
    obtain ⟨r, h0, h1, h2⟩ := hsupp j
    rw [← h0, ← h1, ← h2]
    fin_cases r <;> decide
  have hpoint (j : Fin (2 * N)) :
      ((2 * (modeWord x.1 0 j).val : ℕ) : R) * w j +
          ((2 * (modeWord y.1 1 j).val : ℕ) : R) * w j =
        2 * (((4 : R) - ((modeWord z.1 2 j).val : R)) * w j) := by
    have hr :
        ((modeWord x.1 0 j).val : R) +
            ((modeWord y.1 1 j).val : R) +
            ((modeWord z.1 2 j).val : R) = 4 := by
      have hr' := congrArg (fun n : ℕ ↦ (n : R)) (hsum j)
      push_cast at hr'
      exact hr'
    push_cast
    linear_combination 2 * w j * hr
  calc
    MME.StothersFourth.Phi233.doubledXHash (R := R) (N := N)
          b w (modeWord x.1 0) +
        MME.StothersFourth.Phi233.doubledYHash (R := R) (N := N)
          b w (modeWord y.1 1) =
        4 * b +
          ((∑ j, ((2 * (modeWord x.1 0 j).val : ℕ) : R) * w j) +
            ∑ j, ((2 * (modeWord y.1 1 j).val : ℕ) : R) * w j) := by
      simp only [MME.StothersFourth.Phi233.doubledXHash,
        MME.StothersFourth.Phi233.doubledYHash]
      ring
    _ = 4 * b + ∑ j,
          (((2 * (modeWord x.1 0 j).val : ℕ) : R) * w j +
            ((2 * (modeWord y.1 1 j).val : ℕ) : R) * w j) := by
      rw [Finset.sum_add_distrib]
    _ = 4 * b + ∑ j,
          2 * (((4 : R) - ((modeWord z.1 2 j).val : R)) * w j) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _hj
      exact hpoint j
    _ = (2 : R) * MME.StothersFourth.Phi233.doubledZHash
          (R := R) (N := N) b w (modeWord z.1 2) := by
      rw [← Finset.mul_sum]
      simp only [MME.StothersFourth.Phi233.doubledZHash]
      ring

theorem solution
    {p N alpha beta gamma : ℕ}
    (w : Fin 3 → Fin (2 * N) → ZMod p)
    (shift offset : ZMod p)
    (x y z : CyclicExactEdge N alpha beta gamma)
    (hsupp : CyclicCoordinatewiseSupported x y z) :
    cyclicAffineHash p N alpha beta gamma w shift offset 0 x +
        cyclicAffineHash p N alpha beta gamma w shift offset 1 y =
      2 * cyclicAffineHash p N alpha beta gamma w shift offset 2 z := by
  have ha := basic_doubled_hash_AP
    (2 * offset) (w 0) x.1 y.1 z.1 hsupp.1
  have hb := basic_doubled_hash_AP
    0 (w 1) y.2.1 z.2.1 x.2.1 hsupp.2.1
  have hc := basic_doubled_hash_AP
    offset (w 2) z.2.2 x.2.2 y.2.2 hsupp.2.2
  dsimp only [cyclicAffineHash]
  linear_combination ha - 2 * hb - 2 * hc
