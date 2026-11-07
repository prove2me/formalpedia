-- Prove2me | Theorems.Thm_F3SubsetSum_theorem_1_7
-- name    : F3SubsetSum.theorem_1_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:29:48.121613+00:00
-- url     : https://prove2.me/theorems/421b3b04-02c1-41e8-86ce-687cbe60cba3
-- title:
--   Theorem 1.7 — Binary-Error LWE over $\mathbb F_q$ in time $(m/n)^{O(\lceil n^2/m\rceil)}$, pointwise
-- statement:
--   Let $q\ge3$ be a fixed prime and $\kappa>\log_{q/2}q$. There are a deterministic machine computing a decoder $\mathrm{Dec}$ and constants $C,c>0$ (depending on $q$ and $\kappa$) such that for all $n\ge1$ and $m\ge\kappa n$:
--
--   1. on every input $(A,b)\in\mathbb F_q^{n\times m}\times\mathbb F_q^m$ the machine halts within $(m/n)^{C\lceil n^2/m\rceil}$ steps with output $\mathrm{Dec}(A,b)$;
--   2. for every $s\in\mathbb F_q^n$ and every $e\in\{0,1\}^m$,
--   $$\Pr_{A\sim\mathbb F_q^{n\times m}}\bigl[\mathrm{Dec}(A,A^\top s+e)\neq s\bigr]\le 2^{-cm}.$$
--
--   This is the classical "main ingredient" of the paper: a rigorous form of the sample–time tradeoff that semi-regularity heuristics predicted, with a guarantee for every secret and every binary error.
--
--   Differences from the source:
--   - reading: a deterministic classical algorithm … runs in time (m/n)^{O_{q,κ}(⌈n²/m⌉)} → one multi-stack Turing machine with Boolean alphabets (Turing.TM2ComputableAux Bool Bool, run as HMBinPacking.OutputsWithin) with the codes encodeInstance / encodeSecret, halting within ⌊(m/n)^{C⌈n²/m⌉}⌋ steps on every input; reason: the paper names no machine model; TM and RAM differ by polynomial factors, which the bound absorbs (p.22)
--   - reading: for every m ≥ κ·n there is an algorithm …, O_{q,κ}, Ω_{q,κ} → one machine and constants C, c > 0 chosen before n and m, for every n ≥ 1 and m ≥ κn; reason: the strongest reading; the proof's algorithm is uniform (cases (i)–(iii), p.22)
--   - encoding: n arbitrary → n ≥ 1; reason: m/n is undefined at n = 0
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, Theorem 1.7, p.6 (restated pp.17, 22; proof p.22)

import Mathlib
import Definitions.Def_F3SubsetSum_BinaryErrorLWE
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_F3SubsetSum_MachineCodes

namespace F3SubsetSum

/-- **Theorem 1.7** (Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1, Theorem 1.7,
p.6; restated pp.17, 22; proof p.22): "Let κ > log_{q/2}(q) be any constant. For every m ≥ κ · n,
there is a deterministic classical algorithm that solves Problem 1.5 with probability at least
1 − 2^{−Ω_{q,κ}(m)} and runs in time (m/n)^{O_{q,κ}(⌈n²/m⌉)}."

Here `q ≥ 3` is a fixed prime (Problem 1.5, p.5). One deterministic machine `M`, computing a
decoder `Dec`, works for all `n ≥ 1` and `m ≥ κn`: on every input `(A, b)` it halts within
`(m/n)^{C⌈n²/m⌉}` steps, and for **every** `s ∈ F_qⁿ` and `e ∈ {0,1}^m` its failure probability
`Pr_A[Dec(A, A⊤s + e) ≠ s]` is at most `2^{−cm}` (the pointwise guarantee of Problem 1.5).

**Formalization Note** The algorithm is a multi-stack Turing machine with Boolean alphabets
(`Turing.TM2ComputableAux Bool Bool`) with the input code `encodeInstance` and the
output code `encodeSecret`. `O_{q,κ}` and `Ω_{q,κ}` are read as constants `C, c > 0` depending on
`q` and `κ` only, chosen before `n` and `m`; the machine is chosen before `n` and `m` as well.
`⌈·⌉` is the real ceiling and the power is a real power. `n ≥ 1` because `m/n` is undefined at
`n = 0`. -/
theorem theorem_1_7 (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (κ : ℝ)
    (hκ : Real.logb ((q : ℝ) / 2) q < κ) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (Dec : DecoderFn q) (C c : ℝ), 0 < C ∧ 0 < c ∧
      ∀ n m : ℕ, 1 ≤ n → κ * n ≤ m →
        ComputesWithin M Dec n m ⌊((m : ℝ) / n) ^ (C * (⌈(n : ℝ) ^ 2 / m⌉ : ℝ))⌋₊ ∧
        ∀ (s : Fin n → ZMod q) (e : Fin m → Bool),
          pointwiseFailure Dec n m s e ≤ (2 : ℝ) ^ (-(c * m)) := by sorry

end F3SubsetSum
