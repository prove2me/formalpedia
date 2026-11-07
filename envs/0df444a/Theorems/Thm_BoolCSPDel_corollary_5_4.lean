-- Prove2me | Theorems.Thm_BoolCSPDel_corollary_5_4
-- name    : BoolCSPDel.corollary_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:58:29.114321+00:00
-- url     : https://prove2.me/theorems/01416070-23f1-4620-83f7-5f3d971089fe
-- title:
--   Corollary 5.4 — active-row sparsification in $O_{s_0,b_0}(D\,\mathrm{polylog}(2mD\mu/\delta))$ bits
-- statement:
--   Let $B\in\mathbb Z^{m\times D}$, $m,D\ge1$, have at most $s_0$ nonzero entries and squared norm at most $b_0$ in each row. Given $\mu\ge1$ and $\delta=1/M$, $M\ge3$, one program, reaching rows through the row oracle, processes any strict-turnstile stream with multiplicities at most $\mu$. On every coin tape it uses at most $CD\,\mathrm{polylog}(2mD\mu/\delta)$ cells and outputs at most that many weighted rows. With probability at least $1-\delta$, the rows are distinct and active, the weights are positive, and
--
--   $$B^\top\mathrm{diag}(f)^2B\preceq\sum_{i\in S}w_ib_ib_i^\top+\frac1{4D}I.$$
--
--   The steps after the input is exhausted are polynomial in $m,D,\mu,\delta^{-1}$.
--
--   This gives the upper bound on $n^d$ when combined with the polynomial representation.
--
--   Differences from the source:
--   - reading: "uses … bits", no machine named → cells visited on the program of Program, on every coin tape; reason: p.33, p.55 count stored randomness, output, working space for every choice of seeds
--   - generalization: each row generated from i in polynomial time and polylogarithmic workspace → a unit-cost row oracle, whose answer occupies tape; reason: the generation cost can be charged on top; the bound then holds for every way of producing rows
--   - encoding: real 0 < δ < 1/2 → δ = 1/M, M ≥ 3; reason: any real δ has M = ⌈1/δ⌉ with δ/2 ≤ 1/M ≤ δ; the bound moves by a constant
--   - encoding: positive weights → dyadic weights a / 2^e, a > 0; reason: the output must be written on the tape; the algorithm's weights have this form
--   - reading: "Recovery takes polynomial time in m, D, µ, δ−1 and the row-generation time", with no halting requirement printed → the program halts on every coin tape, and the steps after the input is exhausted are at most (m + D + µ + M + 2)^c; reason: recovery is the computation after the stream (p.55, Lemma A.4); the algorithm uses finitely many seed bits, so it halts on every coin tape
--   - reading: O_{s0,b0}(D polylog(2mDµ/δ)), polylog a fixed power (p.17) → (log(2mDµM + 2))^K with K absolute, chosen before s₀, b₀, and C, c after them; reason: §A.1.3 and Lemma A.4 give a fixed power of log Q with O_{s0,b0} constants
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), Corollary 5.4, pp.31–32; Lemma A.4, p.55

import Mathlib
import Definitions.Def_BoolCSPDel_dictOracle
import Definitions.Def_BoolCSPDel_TurnstileAlg

namespace BoolCSPDel

/-- **Corollary 5.4 (active-row sparsification), machine form.** Bandekar, Sharma, Velusamy, *A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions*, STOC 2027 submission (manuscript sha256 15f83519…), Corollary 5.4, pp.31–32.

One program for all `m, D ≥ 1` and `B` with sparse bounded rows, reaching rows through `query`. On every
coin tape and every legal stream with prefix multiplicities at most `μ` it halts within
`C D polylog(2mDμ/δ)` cells and a list of at most that many rows, with `δ = 1/M`. Off an event of
probability at most `δ` the list consists of distinct active rows with positive weights and
`Bᵀdiag(f)²B ⪯ Σ_{i ∈ S} w_i b_i b_iᵀ + I/(4D)`. Recovery, the steps after the input is exhausted, takes
time polynomial in `m, D, μ, δ⁻¹`.

**Formalization Note.** `0 < δ < 1/2` is `δ = 1/M`, `M ≥ 3`; any real `δ` has `M = ⌈1/δ⌉` with `δ/2 ≤ 1/M ≤ δ`.
Row generation is a unit-cost oracle, whose answer occupies tape. Weights are dyadic. The size and space
bounds hold on every coin tape (Lemma A.4, p.55, "For every choice of random seeds"). -/
theorem corollary_5_4 : ∃ K : ℕ, ∀ s₀ b₀ : ℕ, ∃ (C : ℝ) (c : ℕ) (Pg : Program), 0 < C ∧
    ∀ (m D : ℕ), 1 ≤ m → 1 ≤ D → ∀ B : Matrix (Fin m) (Fin D) ℤ, SparseRows s₀ b₀ B →
    ∀ (μ M : ℕ), 1 ≤ μ → 3 ≤ M → ∀ s : List (Fin m × Bool), IsLegal s → BoundedBy μ s →
      let word := encNat m ++ encNat D ++ encNat μ ++ encNat M ++ updateBits s
      let Bnd : ℝ := C * D * polylog K (2 * m * D * μ * M)
      (∀ coins : ℕ → Bool,
        (∃ cfg, HaltsWith Pg (dictOracle B) word coins cfg ∧ (cfg.space : ℝ) ≤ Bnd ∧
          ∃ l : WeightedList m, TapeHolds cfg.tape 0 (weightedWord l) ∧ (l.length : ℝ) ≤ Bnd) ∧
        ∀ t t', t ≤ t' → (run Pg (dictOracle B) word coins t).input = [] →
          (run Pg (dictOracle B) word coins t').steps ≤
            (run Pg (dictOracle B) word coins t).steps + (m + D + μ + M + 2) ^ c) ∧
      coinMeasure {coins | ¬ ∃ cfg, HaltsWith Pg (dictOracle B) word coins cfg ∧
        ∃ l : WeightedList m, TapeHolds cfg.tape 0 (weightedWord l) ∧ ActiveList (freq s) l ∧
          LoewnerLE (gramR B (freq s))
            (listSum B l + (1 / (4 * (D : ℝ))) • (1 : Matrix (Fin D) (Fin D) ℝ))} ≤
        ENNReal.ofReal (1 / M) := by sorry

end BoolCSPDel
