-- Prove2me | Theorems.Thm_BitDFT_roots_of_unity_machine
-- name    : BitDFT.roots_of_unity_machine
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-24T12:01:39.298407+00:00
-- url     : https://prove2.me/theorems/dcfe0378-ba91-4e53-a4d4-99de34c2e3e8
-- title:
--   Lemma 2.2 — compute roots with error and bit-cost bounds
-- statement:
--   For each positive integer $L$, there is one machine and constant $C>0$ that, on $p,n\ge1$ with $n<2^{Lp}$, returns a fixed-point unit-disc approximation to $e^{2\pi i/n}$ of error less than two ulps within $Cp\ell(p)^2$ transitions. The root is computed from binary parameters; no root table or root oracle is assumed. Positive integer $L$ gives a cofinal formulation of the source constant.
-- source:
--   Harvey and van der Hoeven, Integer multiplication is at least as hard as matrix transposition (2025), https://arxiv.org/abs/2503.22848, Sections 2–3.4; BitDFT transfer specification (24 October 2026) for explicit binary conventions and derived end-to-end formulations. Lemma 2.2 — root construction.

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT

theorem BitDFT.roots_of_unity_machine (L : ℕ) (hL : 1 ≤ L) :
    ∃ A : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧
      ∀ p n : ℕ, 1 ≤ p → 1 ≤ n → n < 2 ^ (L * p) →
        ∃ Z : ℤ × ℤ,
          Computes A (encNat p ++ encNat n) (encComplex (p + 1) Z)
            (C * ((p : ℝ) * (IntMul.lg p : ℝ) ^ 2)) ∧
          inDisc p Z ∧ ulpError p Z (root n) < 2 := by sorry
