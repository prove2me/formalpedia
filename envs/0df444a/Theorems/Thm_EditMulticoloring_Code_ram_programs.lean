-- Prove2me | Theorems.Thm_EditMulticoloring_Code_ram_programs
-- name    : EditMulticoloring.Code.ram_programs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T10:08:39.23547+00:00
-- url     : https://prove2.me/theorems/1c91887c-2f45-412d-86b0-8d6dba66ee7b
-- title:
--   Theorem 1 — fixed RAM programs encode and decode the construction within the stated step costs
-- statement:
--   Fix an alphabet size $q \ge 2$ and $t \ge 1$. There are two RAM programs (`RAM.Program`), an encoder and a decoder, fixed before the block length $n$, a modulus family $n \mapsto p_n$, constants $C_E, C_D > 0$, exponents $d_E, d_D$ and a threshold $n_0 \ge 3$ such that for every $n \ge n_0$, with `P := parameters q t n`: $p_n$ is a valid modulus (`ValidModulus (ceilLog 2 (P.r * P.K + 1)) p_n`); for every message $u$ of length `P.k` the encoder, started in `RAM.initial n` with the message as input, halts accepting and outputs the word `encode t n p_n u` within bit-cost `softBound C_E (6t+2) d_E n` (that is $C_E\, n^{6t+2}(1+\log n)^{d_E}$); and for every received word $y \in [q]^*$ the decoder, started in `RAM.initial n` with $y$ as input, halts with the output `decode t n p_n y` (rejecting exactly when this is `none`) within bit-cost `softBound C_D (7t+2) d_D n`.
--
--   This is the RAM part of Theorem 1 of the paper ("explicit edit codes ... with encoding time ... and decoding time ..."), separated from the combinatorial part, which is `EditMulticoloring.Code.encoder_redundancy` and `EditMulticoloring.Code.decoder_correctness`. The programs may compute the modulus themselves; it is not an input.
-- source:
--   Explicit Edit Codes via Multicoloring, STOC 2027 submission 819 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/819.pdf), p. 3-4, Theorem 1 (running-time part) with Appendix D.

import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine

namespace EditMulticoloring.Code

theorem ram_programs (q t : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) :
    ∃ (encoder decoder : RAM.Program) (modulus : ℕ → ℕ)
      (CE CD : ℝ) (dE dD n₀ : ℕ),
      0 < CE ∧ 0 < CD ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n →
        let P := parameters q t n
        let p := modulus n
        ValidModulus (ceilLog 2 (P.r * P.K + 1)) p ∧
        (∀ u : FixedWord q P.k,
          RAM.Executes encoder n (toWord u)
            (some ((encode t n p (toWord u)).map Fin.val))
            (softBound CE (6 * t + 2) dE n)) ∧
        (∀ y : Word q,
          RAM.Executes decoder n y ((decode t n p y).map (List.map Fin.val))
            (softBound CD (7 * t + 2) dD n)) := by sorry

end EditMulticoloring.Code
