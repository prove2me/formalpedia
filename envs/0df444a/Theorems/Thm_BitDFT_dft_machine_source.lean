-- Prove2me | Theorems.Thm_BitDFT_dft_machine_source
-- name    : BitDFT.dft_machine_source
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-24T12:01:34.762776+00:00
-- url     : https://prove2.me/theorems/019869c2-015b-486b-bf56-2faeff868c76
-- title:
--   Proposition 3.3 — approximate DFT with source precision conditions
-- statement:
--   For any positive integer regime constants $L,L′$ and two multiplication machines bounded by $T,T′$, there is one machine computing the normalised negative-sign DFT in $C(T(m)+nT′(p))$ transitions. Assume $n,p\ge1$, $np\le m$, $\ell(n)<Lp$ and $\ell(p)^2<L′n$. Precision-$p$ input and output are in the unit disc. For every compatible exact unit-disc input of ulp error at most $e$, output error is strictly below $e+12n^2$. All root, packing, rounding and tape costs are included.
-- source:
--   Harvey and van der Hoeven, Integer multiplication is at least as hard as matrix transposition (2025), https://arxiv.org/abs/2503.22848, Sections 2–3.4; BitDFT transfer specification (24 October 2026) for explicit binary conventions and derived end-to-end formulations. Proposition 3.3 — source-regime DFT.

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT

theorem BitDFT.dft_machine_source
    (L L' : ℕ) (hL : 1 ≤ L) (hL' : 1 ≤ L')
    (M M' : IntMul.MultitapeTM) (T T' : ℕ → ℝ)
    (hM : Multiplier M T) (hM' : Multiplier M' T') :
    ∃ A : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧
      ∀ n p m : ℕ, 1 ≤ n → 1 ≤ p → n * p ≤ m →
        IntMul.lg n < L * p → (IntMul.lg p) ^ 2 < L' * n →
        ∀ U : Fin n → ℤ × ℤ, vectorDisc p U →
          ∃ V : Fin n → ℤ × ℤ,
            Computes A (encNat n ++ encNat p ++ encNat m ++ encVector (p + 1) U)
              (encVector (p + 1) V) (C * (T m + (n : ℝ) * T' p)) ∧
            vectorDisc p V ∧
            ∀ (X : Fin n → ℂ) (e : ℝ), (∀ j, ‖X j‖ ≤ 1) → approx p U X e →
              ∀ k, ulpError p (V k) (ndft X k) < e + 12 * (n : ℝ) ^ 2 := by sorry
