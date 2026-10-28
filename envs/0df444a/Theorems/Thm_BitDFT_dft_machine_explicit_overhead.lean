-- Prove2me | Theorems.Thm_BitDFT_dft_machine_explicit_overhead
-- name    : BitDFT.dft_machine_explicit_overhead
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-24T12:01:50.596334+00:00
-- url     : https://prove2.me/theorems/dba38db4-9805-4d36-b81b-1041c6bd188a
-- title:
--   Fourier machine with preparation costs retained
-- statement:
--   Given any multiplier bounded by $T$, one machine computes the normalised DFT for every $n,p\ge1$ with $\ell(n)\le p$. Its runtime is at most a fixed positive constant times $T(np)+nT(p)+p\ell(p)^2+np$. It preserves the fixed-point unit disc and has output error less than input error plus $12n^2$ ulps. Retaining the root and linear-work terms removes the upper restriction on precision relative to length; this is a derived explicit-overhead formulation of the cited construction.
-- source:
--   Harvey and van der Hoeven, Integer multiplication is at least as hard as matrix transposition (2025), https://arxiv.org/abs/2503.22848, Sections 2–3.4; BitDFT transfer specification (24 October 2026) for explicit binary conventions and derived end-to-end formulations. Derived theorem — explicit preparation overhead.

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open BitDFT

theorem BitDFT.dft_machine_explicit_overhead
    (M : IntMul.MultitapeTM) (T : ℕ → ℝ) (hM : Multiplier M T) :
    ∃ A : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧
      ∀ n p : ℕ, 1 ≤ n → 1 ≤ p → IntMul.lg n ≤ p →
        ∀ U : Fin n → ℤ × ℤ, vectorDisc p U →
          ∃ V : Fin n → ℤ × ℤ,
            Computes A (fourierInput p U) (encVector (p + 1) V)
              (C * transferCost T n p) ∧ vectorDisc p V ∧
            ∀ (X : Fin n → ℂ) (e : ℝ), (∀ j, ‖X j‖ ≤ 1) → approx p U X e →
              ∀ k, ulpError p (V k) (ndft X k) < e + 12 * (n : ℝ) ^ 2 := by sorry
