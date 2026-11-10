-- Prove2me | Theorems.Thm_DNFSatMQ_Main_theorem_7_1
-- name    : DNFSatMQ.Main.theorem_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:34:45.674169+00:00
-- url     : https://prove2.me/theorems/82836abf-dd4f-41fd-a0e0-9e37d8756a81
-- title:
--   Theorem 7.1 — Algorithm 4 is a polynomial-time densifier with γ = τ/(4N)
-- statement:
--   Let $f$ be a DNF on $n$ variables with at most $s$ terms and $F = f^{-1}(1)\neq\emptyset$, and let $a_0$ be the constant of Lemma 5.1. For every $\varepsilon,\delta\in(0,1)$, Algorithm 4 with the parameters (10) outputs conjunctions $c_1,\dots,c_m$ with $0\le m\le N$. With $G = \bigcup_i C_i$, with probability at least $1-\delta$,
--   $$|F\setminus G|\le\varepsilon|F|,\qquad \sum_{i=1}^m|C_i|\le\frac{|F|}{\gamma(s,1/\varepsilon,1/\delta)},\qquad \gamma = \frac{\tau}{4N}.$$
--   Moreover $N$ and $\gamma^{-1}$ do not depend on $n$ and are bounded by $\mathrm{poly}(s,1/\varepsilon,\log(1/\delta))$; the algorithm uses $N$ calls to $\mathrm{EX}^+_f$ and $N(n+M)$ calls to $\mathrm{MQ}_f$ and runs in time $\mathrm{poly}(n,s,1/\varepsilon,\log(1/\delta))$.
--
--   The Lean statement has three clauses, all under one quantifier "there is $A>0$ such that for every $a_0\ge A$": (i) Algorithm 4 as a probability law (exact uniform choices) has $m\le N$ on its support and meets both bounds with probability $\ge 1-\delta$; (ii) $N \le c\,(s+1/\varepsilon+\ln(1/\delta))^c$ and $1/\gamma \le c\,(s+1/\varepsilon+\ln(1/\delta))^c$ for one $c$; (iii) there is a program of the fair-coin machine whose decoded output law equals Algorithm 4 exactly and that is a $\gamma$-densifier (Definition 4.1, same $\gamma$) running in time $c\,(n+s+1/\varepsilon+\ln(1/\delta))^c$, whose every run reads exactly $N$ samples ($Nn$ witness bits), asks exactly $N(n+M)$ membership queries, and always outputs at most $N$ conjunctions. The exact-law implementation claim is retained as printed; INSIGHTS I1 gives the bounded-fair-coin obstruction.
--
--   Differences from the source:
--   - encoding: a term: literals on distinct variables → a partial assignment `Conj n = Fin n → Option Bool`; reason: §2 defines terms as noncontradictory; same objects
--   - encoding: coordinates [n] = {1, …, n} and bits {0, 1} → `Fin n` (coordinates 0, …, n−1) and `Bool`; reason: Lean convention; same instances
--   - reading: "a₀, the constant of Lemma 5.1" → ∃ A > 0, ∀ a₀ ≥ A (the same reading as Lemma 5.1); reason: a₀ is "sufficiently large" in Lemma 5.1
--   - encoding: "Algorithm 4 … runs in time poly(n, s, 1/ε, log(1/δ))", with π ∼ U_{S_n} drawn exactly → clause (iii) requires equality of every decoded output-list probability with algorithm4, in addition to the stated call counts and worst-case time; reason: the printed claim concerns Algorithm 4 itself; the exact-sampling obstruction is recorded in INSIGHTS I1, not repaired by substituting another algorithm
--   - encoding: poly(s, 1/ε, log(1/δ)), poly(n, s, 1/ε, log(1/δ)) → c·(s + 1/ε + ln(1/δ))^c and c·(n + s + 1/ε + ln(1/δ))^c for one natural c; reason: for s ≥ 1 these bases are ≥ 1, so every polynomial bound has this form
--   - encoding: "N and γ⁻¹ are independent of n" → `par_N` and `par_γ` are functions of (a₀, s, ε, δ) only; reason: by their type; no clause is needed
--   - encoding: a randomized algorithm with time bound T → a program whose guarantees hold for every coin-tape length L ≥ ⌈T⌉ (Definition 4.1 in `IsDensifier`); reason: a randomized algorithm has an unbounded supply of coins; a program reading its coins in order has this property
--   - encoding: fair random bits, with no additional input in the random-bit supply → HaltsWithin includes CoinsInBounds: every readCoin address is below the supplied tape length; reason: the RAM sentinel must not reveal the externally chosen resource bound; this also makes sampler behavior depend only on its output-word input and fair bits
--   - generalization: Algorithm 4 takes n ≥ 1 → the exact-law correctness clause also allows n = 0; the machine clause keeps n ≥ 1; reason: the empty-coordinate cube has one point and one permutation; a nonempty target is the constant-one function, so the probability guarantee still holds
-- source:
--   Zelin Li, Learning DNF from Satisfying Assignments with Membership Queries, STOC 2027 submission (manuscript sha256 2e246dc4…2670), Theorem 7.1, p. 27 (PDF 28)

import Mathlib
import Definitions.Def_DNFSatMQ_Main_Scan
import Definitions.Def_DNFSatMQ_Main_Machine
open TargetedSamplers

namespace DNFSatMQ.Main

/-- Theorem 7.1 (p. 27). Clauses: (i) Algorithm 4 (exact uniform choices) outputs at most `N`
conjunctions and meets the densifier guarantees with probability `≥ 1 − δ`; (ii) `N` and `γ⁻¹`
are bounded by a polynomial in `s, 1/ε, log(1/δ)` (they do not take `n` as an argument);
(iii) a fair-coin implementation has exactly the output law of Algorithm 4, makes exactly `N`
calls to `EX⁺_f` and `N(n + M)` calls to `MQ_f`, and runs in polynomial time.
The exact-law claim is retained as printed; finding I1 records the bounded-coin obstruction. -/
theorem theorem_7_1 :
    ∃ A : ℝ, 0 < A ∧ ∀ a0 : ℝ, A ≤ a0 →
      (∀ (n s : ℕ) (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        ∀ φ : SamplingAC0.DNF (Fin n), φ.length ≤ s → ∀ hF : (satSet φ).Nonempty,
          (∀ cs ∈ (algorithm4 a0 s ε δ (satSet φ) hF).support, cs.length ≤ par_N a0 s ε δ) ∧
          prob (algorithm4 a0 s ε δ (satSet φ) hF)
              {cs | (((satSet φ) \ listUnion cs).card : ℝ) ≤ ε * (satSet φ).card ∧
                (listVolume cs : ℝ) ≤ (satSet φ).card / par_γ a0 s ε δ} ≥ 1 - δ) ∧
      (∃ c : ℕ, ∀ (s : ℕ) (ε δ : ℝ), 1 ≤ s → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        (par_N a0 s ε δ : ℝ) ≤ c * ((s : ℝ) + 1 / ε + Real.log (1 / δ)) ^ c ∧
        1 / par_γ a0 s ε δ ≤ c * ((s : ℝ) + 1 / ε + Real.log (1 / δ)) ^ c) ∧
      (∃ (P : Program) (c : ℕ),
        IsDensifier P (fun _ s a b => par_γ a0 s (1 / a) (1 / b))
          (fun n s a b => c * ((n : ℝ) + s + a + Real.log b) ^ c) ∧
        ∀ (n s : ℕ), 1 ≤ n → 1 ≤ s → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
          ∀ φ : SamplingAC0.DNF (Fin n), φ.length ≤ s → ∀ hF : (satSet φ).Nonempty,
          ∀ (L : ℕ), ⌈c * ((n : ℝ) + s + 1 / ε + Real.log (1 / δ)) ^ c⌉₊ ≤ L →
          (∀ cs : List (Conj n),
            probCoinsSamples L (satSet φ) (fun r w =>
              ∃ y, outWord P (learnerTapes s (satSet φ) φ.eval ε (some δ) r w) = some y ∧
                decodeConjList n y = some cs) =
              (algorithm4 a0 s ε δ (satSet φ) hF cs).toReal) ∧
          ∀ (r : Fin L → Bool) (w : Fin L → {x // x ∈ satSet φ}),
            witnessRead P (learnerTapes s (satSet φ) φ.eval ε (some δ) r w) =
                par_N a0 s ε δ * n ∧
            mqCount P (learnerTapes s (satSet φ) φ.eval ε (some δ) r w) =
                par_N a0 s ε δ * (n + par_M a0 s ε δ) ∧
            ∀ (y : List Bool) (cs : List (Conj n)),
              outWord P (learnerTapes s (satSet φ) φ.eval ε (some δ) r w) = some y →
              decodeConjList n y = some cs → cs.length ≤ par_N a0 s ε δ) := by sorry

end DNFSatMQ.Main
