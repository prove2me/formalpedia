-- Prove2me | Theorems.Thm_BitDFT_normalized_convolution_machine
-- name    : BitDFT.normalized_convolution_machine
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-24T12:01:46.862433+00:00
-- url     : https://prove2.me/theorems/1c8aa600-243a-476b-9094-22cb4279e2aa
-- title:
--   Proposition 3.1 — numerical convolution from binary multipliers
-- statement:
--   For any positive integer regime constants $L,L′$ and any two actual multiplication machines with pointwise bounds $T,T′$, a uniform machine computes the normalised middle convolution of lengths $n$ and $2n-1$ in $C(T(m)+nT′(p))$ transitions. The conditions are $n,p\ge1$, $np\le m$, $\ell(n)<Lp$ and $\ell(p)<L′n$. Inputs and output are precision-$p$ unit-disc Gaussian pairs. For all compatible exact unit-disc inputs with ulp error bounds $e_F,e_G$, each output error is strictly below $e_F+e_G+2$.
-- source:
--   Harvey and van der Hoeven, Integer multiplication is at least as hard as matrix transposition (2025), https://arxiv.org/abs/2503.22848, Sections 2–3.4; BitDFT transfer specification (24 October 2026) for explicit binary conventions and derived end-to-end formulations. Proposition 3.1 — complete convolution machine.

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT

theorem BitDFT.normalized_convolution_machine
    (L L' : ℕ) (hL : 1 ≤ L) (hL' : 1 ≤ L')
    (M M' : IntMul.MultitapeTM) (T T' : ℕ → ℝ)
    (hM : Multiplier M T) (hM' : Multiplier M' T') :
    ∃ A : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧
      ∀ n p m : ℕ, 1 ≤ n → 1 ≤ p → n * p ≤ m →
        IntMul.lg n < L * p → IntMul.lg p < L' * n →
        ∀ (U : Fin n → ℤ × ℤ) (V : Fin (2 * n - 1) → ℤ × ℤ),
          vectorDisc p U → vectorDisc p V →
          ∃ W : Fin n → ℤ × ℤ,
            Computes A (encNat n ++ encNat p ++ encNat m ++
              encVector (p + 1) U ++ encVector (p + 1) V)
              (encVector (p + 1) W) (C * (T m + (n : ℝ) * T' p)) ∧
            vectorDisc p W ∧
            ∀ (F : Fin n → ℂ) (G : Fin (2 * n - 1) → ℂ) (eF eG : ℝ),
              (∀ j, ‖F j‖ ≤ 1) → (∀ j, ‖G j‖ ≤ 1) →
              approx p U F eF → approx p V G eG →
              ∀ k, ulpError p (W k) (middle F G k) < eF + eG + 2 := by sorry
