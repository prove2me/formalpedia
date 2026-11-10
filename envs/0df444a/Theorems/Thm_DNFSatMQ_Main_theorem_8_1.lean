-- Prove2me | Theorems.Thm_DNFSatMQ_Main_theorem_8_1
-- name    : DNFSatMQ.Main.theorem_8_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:34:40.003465+00:00
-- url     : https://prove2.me/theorems/80eb88b6-269d-4da0-a02c-6a95d6f1b7ee
-- title:
--   Theorem 8.1 — Feldman's PTF learner: with MQ access, a polynomial p with Pr[1{p ≥ 0} ≠ f] ≤ ε, in polynomial time and size
-- statement:
--   There is a randomized algorithm that, given $d\ge0$, $s\ge1$, $\varepsilon,\delta\in(0,1)$ and membership-query access to an $s$-term DNF $f:\{0,1\}^d\to\{0,1\}$, returns a polynomial $p$. With probability at least $1-\delta$ the PTF $h(x) = \mathbf 1\{p(x)\ge0\}$ satisfies
--   $$\Pr_{x\sim U_d}[h(x)\ne f(x)]\le\varepsilon .$$
--   The running time and the size of $p$ are $\mathrm{poly}(d,s,1/\varepsilon,\log(1/\delta))$. The paper cites [Fel12, Corollary 15 and Theorem 21] and proves it in Appendix A; it is the uniform-distribution learner used for Theorem 1.2.
--
--   In Lean: one program and one $c$ such that every run halts within $\lceil c(d+s+1/\varepsilon+\ln(1/\delta))^c\rceil$, every run outputs a decodable polynomial expression of size at most $c(d+s+1/\varepsilon+\ln(1/\delta))^c$, and with probability $\ge1-\delta$ its output decodes to a polynomial expression whose PTF has error $\le\varepsilon$.
--
--   Differences from the source:
--   - encoding: coordinates [n] = {1, …, n} and bits {0, 1} → `Fin n` (coordinates 0, …, n−1) and `Bool`; reason: Lean convention; same instances
--   - encoding: poly(d, s, 1/ε, log(1/δ)) → c·(d + s + 1/ε + ln(1/δ))^c for one natural c fixed before the input; reason: s ≥ 1, so the base is ≥ 1 and every polynomial bound has this form
--   - reading: "the size of p" → the size of the polynomial expression output (nodes plus bit lengths of indices and constants), on every run; reason: "length of a polynomial expression" (p. 2); counting constant bits is the stronger reading
--   - generalization: ε, δ given to the algorithm → ε, δ any reals, accessed by comparison queries; reason: covers every rational encoding; the time bound does not depend on it
--   - encoding: a randomized algorithm with membership queries → a program of the fair-coin RAM with input d, s in unary and MQ_f as its oracle; bounds for every coin-tape length L ≥ the time bound; reason: the paper names no machine model; a randomized algorithm has an unbounded supply of coins
--   - encoding: fair random bits, with no additional input in the random-bit supply → HaltsWithin includes CoinsInBounds: every readCoin address is below the supplied tape length; reason: the RAM sentinel must not reveal the externally chosen resource bound; this also makes sampler behavior depend only on its output-word input and fair bits
--   - encoding: returns a polynomial p; its size is polynomial → every run outputs a decodable expression of the stated size; reason: the source randomizes the error guarantee, not the existence of the returned polynomial
--   - encoding: a polynomial expression for the returned real polynomial → PolyExpr uses rational constants, including bit lengths in size; reason: the constructive expressions in Appendix A and the combination on PDF 31 use rational coefficients; these are real polynomials, with polynomial bit length
-- source:
--   Zelin Li, Learning DNF from Satisfying Assignments with Membership Queries, STOC 2027 submission (manuscript sha256 2e246dc4…2670), Theorem 8.1, p. 30 (PDF 31)

import Mathlib
import Definitions.Def_DNFSatMQ_Main_Machine
open TargetedSamplers

namespace DNFSatMQ.Main

/-- Theorem 8.1 (p. 30; Feldman's learner, proved in Appendix A). -/
theorem theorem_8_1 :
    ∃ (P : Program) (c : ℕ), ∀ (d s : ℕ), 1 ≤ s → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ∀ φ : SamplingAC0.DNF (Fin d), φ.length ≤ s →
      ∀ L : ℕ, ⌈c * ((d : ℝ) + s + 1 / ε + Real.log (1 / δ)) ^ c⌉₊ ≤ L →
        (∀ r : Fin L → Bool, HaltsWithin P (udTapes s φ.eval ε δ r)
            ⌈c * ((d : ℝ) + s + 1 / ε + Real.log (1 / δ)) ^ c⌉₊) ∧
        (∀ r : Fin L → Bool, ∃ y p,
          outWord P (udTapes s φ.eval ε δ r) = some y ∧ decodePolyExpr d y = some p ∧
          (p.size : ℝ) ≤ c * ((d : ℝ) + s + 1 / ε + Real.log (1 / δ)) ^ c) ∧
        probCoins L (fun r => ∃ y p, outWord P (udTapes s φ.eval ε δ r) = some y ∧
          decodePolyExpr d y = some p ∧
          uniformError (fun x => decide (0 ≤ p.eval x)) φ.eval ≤ ε) ≥ 1 - δ := by sorry

end DNFSatMQ.Main
