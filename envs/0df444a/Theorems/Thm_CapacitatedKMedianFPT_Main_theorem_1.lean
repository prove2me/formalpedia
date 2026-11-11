-- Prove2me | Theorems.Thm_CapacitatedKMedianFPT_Main_theorem_1
-- name    : CapacitatedKMedianFPT.Main.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:15:35.793602+00:00
-- url     : https://prove2.me/theorems/2844026d-bcec-4e66-8a9c-3851e77993db
-- title:
--   Theorem 1 — deterministic (1 + 2/e + ε)-approximation for capacitated k-median in FPT time
-- statement:
--   There is a deterministic algorithm $A$ and a computable function $f$ such that, for every feasible instance $I$ of capacitated $k$-median and every rational $\varepsilon>0$, $A$ runs in time $f(k,\varepsilon)\cdot|I|^{O(1)}$ and outputs a feasible solution, namely $k$ distinct open facilities $S\subseteq F$ and an assignment $\varphi:C\to S$ with $|\varphi^{-1}(s)|\le U_s$ for every $s\in S$, of cost
--   $$\sum_{c\in C}d(c,\varphi(c))\le\Bigl(1+\frac2e+\varepsilon\Bigr)\mathrm{OPT}(I).$$
--
--   Here $|I|$ is the input length. One program, one computable $f$ and one exponent work for all instances and all $\varepsilon$. The theorem improves the $(3+\varepsilon)$ FPT approximation of Cohen-Addad and Li and matches the PIH lower bound $1+2/e$ for uncapacitated $k$-median.
--
--   **Formalization Note** The program receives $\varepsilon$ followed by the encoded instance. Its running time is the logarithmic cost of `Machine`, bounded by $f(k,\varepsilon)\cdot\max(2,|I|)^e$; $f$ receives $\varepsilon$ as the pair (numerator, denominator). Distances are arbitrary rationals; no integrality, bound on distances, positive optimum, disjointness of $C$ and $F$ or uniform capacity is assumed.
--
--   Differences from the source:
--
--   - encoding: an instance I with input length |I| → a rational instance in the standard encoding (`RatInstance.encode`), |I| its total bit length; reason: an input length presupposes a finite exact representation; binary rationals are the standard one, and any rational instance is an instance of the source
--   - encoding: a deterministic algorithm and its running time (model not fixed) → a program of the deterministic rational-cell RAM (`Machine`), time in logarithmic (bit) cost; reason: logarithmic cost is polynomially equivalent to Turing machines, so the form f(k, ε)·|I|^O(1) is model independent
--   - encoding: time f(k, ε)·|I|^O(1) for a computable f → ∃ computable f : ℕ × ℕ × ℕ → ℕ evaluated at (k, num ε, den ε) and ∃ e with time ≤ f(k, ε)·max(2, |I|)^e; reason: the meaning of O(1) with one exponent; ε is represented by its numerator and denominator; |I| ≥ 2 always, so the max changes nothing
--   - encoding: the sum of the k largest capacities is at least |C| → some k facilities have total capacity at least |C|; reason: equivalent conditions
--   - encoding: cost at most ρ·OPT → cost at most ρ times the cost of every solution; reason: OPT is the minimum over the finitely many assignments of C, so the two are equivalent
--   - encoding: outputs (S, φ) → S and φ read from fixed memory cells (`RatInstance.IsSolutionOutput`), the k facilities distinct; reason: the source does not fix an output format
-- source:
--   Aditya Anand, Yichen Huang, Ragesh Jaiswal, Amit Kumar, Euiwoong Lee, Jatin Yadav, A Tight FPT Approximation for Capacitated k-Median, STOC 2027 submission #1646 (October 2026), p. 1–2, Theorem 1; p. 5, §2 Instances (instance, solution, feasibility, OPT); proof p. 19, §6

import Mathlib
import Definitions.Def_CapacitatedKMedianFPT_Main_Instance
import Definitions.Def_CapacitatedKMedianFPT_Main_Machine
import Definitions.Def_CapacitatedKMedianFPT_Main_Encoding

set_option autoImplicit false

namespace CapacitatedKMedianFPT.Main

/-- **Theorem 1** (p. 1–2). There is one deterministic program `A`, one computable `f` and one
exponent `e` such that on every valid feasible instance `I` (rational distances, standard encoding)
and every rational `ε > 0`, `A` halts in bit-cost time `f(k, ε) · max(2, |I|)^e` and outputs `k`
distinct facilities and a capacity-respecting assignment of cost at most `(1 + 2/e + ε) · OPT`.
`ε` is passed to `f` as `(numerator, denominator)`. -/
theorem theorem_1 :
    ∃ (A : Program) (f : ℕ × ℕ × ℕ → ℕ) (e : ℕ), Computable f ∧
      ∀ (I : RatInstance) (ε : ℚ), I.toInstance.IsValid → I.toInstance.Feasible → 0 < ε →
        ∃ (mem : Memory) (s : Stats), RunsTo A zeroOracle (ε :: I.encode) mem s ∧
          s.logTime ≤ f (I.k, ε.num.toNat, ε.den) * (max 2 (inputLength I.encode)) ^ e ∧
          I.IsSolutionOutput (1 + 2 / Real.exp 1 + (ε : ℝ)) mem := by sorry

end CapacitatedKMedianFPT.Main
