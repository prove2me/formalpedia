-- Prove2me | solution 1 for mme_stothers_phi233_cyclic_affine_hash_AP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:34:55.446598+00:00
-- url     : https://prove2.me/submissions/88d6fe18-6114-42b7-8a17-d833c1c8db6c

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_affine_hash

open MME.StothersFourth.Phi233

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p N alpha beta gamma delta : ℕ}
    (w : Fin 3 → Fin (2 * N) → ZMod p)
    (shift offset : ZMod p)
    (x y z : CyclicAmbientEdge N alpha beta gamma delta)
    (hsupp : CyclicCoordinatewiseSupported x y z) :
    cyclicAffineHash p N alpha beta gamma delta w shift offset 0 x +
        cyclicAffineHash p N alpha beta gamma delta w shift offset 1 y =
      2 * cyclicAffineHash p N alpha beta gamma delta w shift offset 2 z := by
  have hbasic (b : ZMod p) (v : Fin (2 * N) → ZMod p)
      (a : ProfileAddress N) (haSupp : CoordinatewiseSupported a) :
      doubledXHash b v (a 0) + doubledYHash b v (a 1) =
        2 * doubledZHash b v (a 2) := by
    have hsum (j : Fin (2 * N)) :
        (a 0 j).val + (a 1 j).val + (a 2 j).val = 4 := by
      obtain ⟨r, hr⟩ := haSupp j
      have h0 := congrFun hr (0 : Fin 3)
      have h1 := congrFun hr (1 : Fin 3)
      have h2 := congrFun hr (2 : Fin 3)
      fin_cases r <;>
        simp [addressType, pattern, MME.cwSquareBlockType] at h0 h1 h2 ⊢ <;>
        omega
    have hpoint (j : Fin (2 * N)) :
        ((2 * (a 0 j).val : ℕ) : ZMod p) * v j +
            ((2 * (a 1 j).val : ℕ) : ZMod p) * v j =
          2 * (((4 : ZMod p) - ((a 2 j).val : ZMod p)) * v j) := by
      have hr : ((a 0 j).val : ZMod p) + ((a 1 j).val : ZMod p) +
          ((a 2 j).val : ZMod p) = 4 := by
        have hr' := congrArg (fun n : ℕ ↦ (n : ZMod p)) (hsum j)
        push_cast at hr'
        exact hr'
      push_cast
      linear_combination 2 * v j * hr
    calc
      doubledXHash b v (a 0) + doubledYHash b v (a 1) =
          4 * b +
            ((∑ j, ((2 * (a 0 j).val : ℕ) : ZMod p) * v j) +
              ∑ j, ((2 * (a 1 j).val : ℕ) : ZMod p) * v j) := by
        simp only [doubledXHash, doubledYHash]
        ring
      _ = 4 * b + ∑ j,
            (((2 * (a 0 j).val : ℕ) : ZMod p) * v j +
              ((2 * (a 1 j).val : ℕ) : ZMod p) * v j) := by
        rw [Finset.sum_add_distrib]
      _ = 4 * b + ∑ j,
            2 * (((4 : ZMod p) - ((a 2 j).val : ZMod p)) * v j) := by
        congr 1
        apply Finset.sum_congr rfl
        intro j _hj
        exact hpoint j
      _ = 2 * doubledZHash b v (a 2) := by
        rw [← Finset.mul_sum]
        simp only [doubledZHash]
        ring
  have ha :
      doubledXHash (2 * offset) (w 0) (x.1.1 0) +
          doubledYHash (2 * offset) (w 0) (y.1.1 1) =
        2 * doubledZHash (2 * offset) (w 0) (z.1.1 2) := by
    exact
      (hbasic (2 * offset) (w 0)
        (mixedAddress x.1 y.1 z.1) hsupp.1)
  have hb :
      doubledXHash 0 (w 1) (y.2.1.1 0) +
          doubledYHash 0 (w 1) (z.2.1.1 1) =
        2 * doubledZHash 0 (w 1) (x.2.1.1 2) := by
    exact
      (hbasic 0 (w 1)
        (mixedAddress y.2.1 z.2.1 x.2.1) hsupp.2.1)
  have hc :
      doubledXHash offset (w 2) (z.2.2.1 0) +
          doubledYHash offset (w 2) (x.2.2.1 1) =
        2 * doubledZHash offset (w 2) (y.2.2.1 2) := by
    exact
      (hbasic offset (w 2)
        (mixedAddress z.2.2 x.2.2 y.2.2) hsupp.2.2)
  dsimp only [cyclicAffineHash]
  linear_combination ha - 2 * hb - 2 * hc
