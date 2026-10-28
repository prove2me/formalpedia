-- Prove2me | Theorems.Thm_BitDFT_input_rewrite_machine
-- name    : BitDFT.input_rewrite_machine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T17:37:33.456366+00:00
-- url     : https://prove2.me/theorems/72a8ca99-eec4-44c0-b224-ed63955e3f83
-- title:
--   Actual request-header rewriting and arbitrary child execution preserve the transfer-cost bound
-- statement:
--   Let T be any pointwise integer-multiplication bound realized by a machine M, and let A be any finite child machine. For every positive constant C there exists a fixed native wrapper B and positive D such that any computation by A on the Fourier input at guarded precision q, with cost at most C times the transfer cost, is reproduced by B from the requested input with the identical output and cost at most D times the same transfer cost. The construction works for every output word and input vector, without disc assumptions or monotonicity of T.
-- source:
--   The input-rewriting and arbitrary-call portion of the output-rescaling wrapper is now an actual machine theorem. This theorem does not perform the remaining multiplication of output coordinates by n, and it does not construct the normalized DFT machine.

import Definitions.Def_BitDFT_NativeChildOutput
open BitDFT IntMul

theorem BitDFT.input_rewrite_machine (M : MultitapeTM) (T : ℕ → ℝ) (hM : Multiplier M T)
    (A : MultitapeTM) (C : ℝ) (hC : 0 < C) :
    ∃ B : MultitapeTM, ∃ D : ℝ, 0 < D ∧
      ∀ n b : ℕ, 1 ≤ n → 1 ≤ b → ∀ U : Fin n → ℤ × ℤ, ∀ w : List Bool,
        Computes A (fourierInput (guardPrecision n b) U) w (C*transferCost T n (guardPrecision n b)) →
        Computes B (requestedInput b U) w (D*transferCost T n (guardPrecision n b)) := by sorry
