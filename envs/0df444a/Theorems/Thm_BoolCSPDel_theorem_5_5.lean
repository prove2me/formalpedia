-- Prove2me | Theorems.Thm_BoolCSPDel_theorem_5_5
-- name    : BoolCSPDel.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:58:28.160384+00:00
-- url     : https://prove2.me/theorems/2c989a24-83dc-478a-98c7-577fe2271993
-- title:
--   Theorem 5.5 — regularized dictionary recovery, (5.6)
-- statement:
--   Let $B\in\mathbb Z^{m\times D}$ be a sparse row dictionary, $\mu\ge1$, $\varepsilon=1/E$ with $E\ge8$, $\delta=1/M$ with $M\ge3$, $\lambda=2^{-L}$, and $Q=2+mD\mu/(\varepsilon\delta\lambda)$. One program, reaching rows through the row oracle, processes any strict-turnstile stream with multiplicities at most $\mu$; put $G=B^\top\mathrm{diag}(f)^2B$. On every coin tape it uses at most $CD\varepsilon^{-4}\mathrm{polylog}\,Q$ cells and outputs at most $CD\varepsilon^{-2}\mathrm{polylog}\,Q$ weighted rows, and its time per update and its time after the stream are polynomial in $m,D,\mu,\varepsilon^{-1},\delta^{-1},\lambda^{-1}$. With probability at least $1-\delta$, the rows are distinct and active, the weights are positive, and
--
--   $$(1-\varepsilon)(G+\lambda I)\preceq W+\lambda I\preceq(1+\varepsilon)(G+\lambda I).\tag{5.6}$$
--
--   This is the algorithmic core of the upper bound.
--
--   **Formalization Note** The time clause bounds the steps during any interval in which the remaining input does not change, which covers each update and the time after the stream.
--
--   Differences from the source:
--   - reading: "uses … bits", no machine named → cells visited on the program of Program, on every coin tape; reason: p.33, p.55 count stored randomness, output, working space for every choice of seeds
--   - generalization: each row generated from i in polynomial time and polylogarithmic workspace → a unit-cost row oracle, whose answer occupies tape; reason: the generation cost can be charged on top; the bound then holds for every way of producing rows
--   - encoding: real 0 < δ < 1/2 → δ = 1/M, M ≥ 3; reason: any real δ has M = ⌈1/δ⌉ with δ/2 ≤ 1/M ≤ δ; the bound moves by a constant
--   - encoding: positive weights → dyadic weights a / 2^e, a > 0; reason: the output must be written on the tape; the algorithm's weights have this form
--   - encoding: real 0 < ε ≤ 1/8 → ε = 1/E, E ≥ 8; reason: any real ε has E = ⌈1/ε⌉ with ε/2 ≤ 1/E ≤ ε; the bound moves by a constant
--   - reading: "The time per update and the time after the stream are polynomial in m, D, µ, ε−1, δ−1, λ−1", with no halting requirement printed → the program halts on every coin tape, and over any interval of the run in which the remaining input does not change the steps grow by at most (m + D + µ + E + M + 2^L + 2)^c; reason: an update is read bit by bit, so these intervals cover the work on each update and, once the input is exhausted, the work after the stream; the algorithm uses finitely many seed bits
--   - reading: O_{s0,b0}(Dε−4 polylog Q), polylog a fixed power (p.17) → (log(Q + 2))^K with K absolute, chosen before s₀, b₀, and C, c after them; reason: §A.1.3 and Lemma A.4 give a fixed power of log Q with O_{s0,b0} constants
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), Theorem 5.5, pp.32–33; restated p.54

import Mathlib
import Definitions.Def_BoolCSPDel_dictOracle
import Definitions.Def_BoolCSPDel_TurnstileAlg

namespace BoolCSPDel

/-- **Theorem 5.5 (regularized dictionary recovery), machine form.** Bandekar, Sharma, Velusamy, *A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions*, STOC 2027 submission (manuscript sha256 15f83519…), Theorem 5.5, pp.32–33,
restated p.54.

One program for all `m, D ≥ 1`, `B` with sparse bounded rows, `μ ≥ 1`, `ε = 1/E` with `E ≥ 8`, `δ = 1/M` with
`M ≥ 3`, `λ = 2^{-L}`, and `Q = 2 + mDμ/(εδλ)`. On every coin tape and every legal stream with multiplicities
at most `μ`: it halts within `C D ε⁻⁴ polylog Q` cells and a list of at most `C D ε⁻² polylog Q` rows; the steps
during which the remaining input does not change, which covers the time per update and the time after
the stream, are polynomial in `m, D, μ, ε⁻¹, δ⁻¹, λ⁻¹`. Off an event of probability at most `δ` the list consists
of distinct active rows with positive weights and `(1 − ε)(G + λI) ⪯ W + λI ⪯ (1 + ε)(G + λI)`, display (5.6).

**Formalization Note.** Parameters as in `corollary_5_4`. A real `ε ∈ (0, 1/8]` has `E = ⌈1/ε⌉` with
`ε/2 ≤ 1/E ≤ ε`. A bit of the input is read at the boundary of each interval of constant remaining input. -/
theorem theorem_5_5 : ∃ K : ℕ, ∀ s₀ b₀ : ℕ, ∃ (C : ℝ) (c : ℕ) (Pg : Program), 0 < C ∧
    ∀ (m D : ℕ), 1 ≤ m → 1 ≤ D → ∀ B : Matrix (Fin m) (Fin D) ℤ, SparseRows s₀ b₀ B →
    ∀ (μ E M L : ℕ), 1 ≤ μ → 8 ≤ E → 3 ≤ M → ∀ s : List (Fin m × Bool), IsLegal s → BoundedBy μ s →
      let word := encNat m ++ encNat D ++ encNat μ ++ encNat E ++ encNat M ++ encNat L ++ updateBits s
      let Q : ℝ := 2 + m * D * μ * E * M * 2 ^ L
      let lam : ℝ := 1 / 2 ^ L
      let eps : ℝ := 1 / E
      let G := gramR B (freq s)
      let I : Matrix (Fin D) (Fin D) ℝ := 1
      (∀ coins : ℕ → Bool,
        (∃ cfg, HaltsWith Pg (dictOracle B) word coins cfg ∧
          (cfg.space : ℝ) ≤ C * D * (E : ℝ) ^ 4 * polylog K Q ∧
          ∃ l : WeightedList m, TapeHolds cfg.tape 0 (weightedWord l) ∧
            (l.length : ℝ) ≤ C * D * (E : ℝ) ^ 2 * polylog K Q) ∧
        ∀ t t', t ≤ t' →
          (run Pg (dictOracle B) word coins t).input.length =
            (run Pg (dictOracle B) word coins t').input.length →
          (run Pg (dictOracle B) word coins t').steps ≤
            (run Pg (dictOracle B) word coins t).steps + (m + D + μ + E + M + 2 ^ L + 2) ^ c) ∧
      coinMeasure {coins | ¬ ∃ cfg, HaltsWith Pg (dictOracle B) word coins cfg ∧
        ∃ l : WeightedList m, TapeHolds cfg.tape 0 (weightedWord l) ∧ ActiveList (freq s) l ∧
          LoewnerLE ((1 - eps) • (G + lam • I)) (listSum B l + lam • I) ∧
          LoewnerLE (listSum B l + lam • I) ((1 + eps) • (G + lam • I))} ≤
        ENNReal.ofReal (1 / M) := by sorry

end BoolCSPDel
