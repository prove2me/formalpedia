-- Prove2me | Theorems.Thm_DNFSatMQ_Main_theorem_1_2
-- name    : DNFSatMQ.Main.theorem_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:34:16.734244+00:00
-- url     : https://prove2.me/theorems/f5f31a2f-700f-4739-9b77-a868d1532f41
-- title:
--   Theorem 1.2 — polynomial-time learning from satisfying assignments of DNFs with a PTF hypothesis and a sampler
-- statement:
--   **Problem 1.1.** Given $n,s\ge1$, $\varepsilon\in(0,1/2)$, and access to $\mathrm{EX}^+_f$ (independent samples from $U_F$, $F = f^{-1}(1)\neq\emptyset$) and $\mathrm{MQ}_f$ for an unknown $s$-term DNF $f$ on $n$ variables, output a Boolean hypothesis $h$ together with a sampling procedure with output distribution $D_h$ on $\{0,1\}^n\cup\{\bot\}$. With probability at least $2/3$, $H = h^{-1}(1)$ is nonempty and
--   $$d_{TV}(U_H,U_F)\le\frac\varepsilon2,\qquad d_{TV}(D_h,U_H)\le\frac\varepsilon2,$$
--   where $U_F, U_H$ give $\bot$ probability zero. The sampling procedure uses $\mathrm{poly}(n,s,1/\varepsilon)$ random bits and depends only on the learner's output, with no further access to $\mathrm{EX}^+_f$ and $\mathrm{MQ}_f$.
--
--   **Theorem 1.2.** There is a randomized algorithm that solves Problem 1.1 in time $\mathrm{poly}(n,s,1/\varepsilon)$ and outputs a hypothesis $h$ which is a PTF of size $\mathrm{poly}(n,s,1/\varepsilon)$; the output sampling procedure generates each sample in time $\mathrm{poly}(n,s,1/\varepsilon)$. Here a PTF is $x\mapsto\mathbf 1\{p(x)\ge0\}$ and its size is the length of a polynomial expression for $p$, stored in factored form.
--
--   In Lean: there are one learner program $P_L$, one sampler program $P_S$ (both programs of the published fair-coin RAM) and one $c\in\mathbb N$, chosen before the input, such that for all $n,s\ge1$, $\varepsilon\in(0,1/2)$ and every DNF $\varphi$ with at most $s$ terms and $F\ne\emptyset$, with $B = c\,(n+s+\lceil1/\varepsilon\rceil)^c$: $P_L$ halts within $B$ on every coin string and every sample stream; on every word $y$ it outputs, $P_S$ run on $y$ with $B$ fair coins and no oracle halts within $B$; and with probability $\ge2/3$ over $P_L$'s $B$ coins and $B$ samples, $y$ starts with a polynomial expression $p$ of size $\le B$ whose PTF set $H$ is nonempty and satisfies both distance bounds, $D_h$ being the output law of $P_S$ on $y$.
--
--   Differences from the source:
--   - encoding: poly(n, s, 1/ε) (learning time, sampler random bits, time per sample, PTF size) → B = c·(n + s + ⌈1/ε⌉)^c for one natural c fixed with the programs before the input; reason: for n, s ≥ 1 and ε ∈ (0, 1/2) every polynomial bound is dominated by such a B
--   - encoding: a randomized algorithm (no machine model is named) → a program of the published log-cost RAM `TargetedSamplers.Program`: input n, s in unary, B fair coins, EX⁺_f as a read-once witness tape of B independent U_F samples, MQ_f as the oracle on 0-tagged queries; time is worst case over all coins and streams; reason: polynomial time is robust across reasonable models; the probability is over the coins and samples jointly, as in Problem 1.1
--   - generalization: ε ∈ (0, 1/2) given to the learner → ε any real in (0, 1/2), available only through comparison queries "ε ≤ v?" for rational v; the time bound does not depend on how ε is written; reason: covers every rational encoding of ε; a bit machine could not even read an arbitrary rational in time poly(1/ε)
--   - reading: "a PTF of size poly(n, s, 1/ε)", explicitly represented → the output word starts with a polynomial expression p (`decodePolyExpr`), h = 1{p ≥ 0}; size(p) counts nodes plus the bit lengths of variable indices and constants; reason: "its size is the length of a polynomial expression for p" (p. 2); counting constant bits is the stronger reading; never the number of monomials
--   - encoding: a sampling procedure that depends only on the learner's output, uses poly random bits, no further oracle access → one fixed sampler program run on the learner's output word with exactly B fair coins, an empty witness tape and no oracle; an output of length ≠ n counts as ⊥; reason: literal machine reading of Problem 1.1
--   - encoding: D_h, U_H, U_F on {0,1}ⁿ ∪ {⊥} → laws on `Option (Fin n → Bool)` (`none` = ⊥); U_H, U_F pushed forward by `some`; d_TV is `SSNonExt.TV`; reason: same objects
--   - encoding: an s-term DNF f with F ≠ ∅ → f = φ.eval for a published `SamplingAC0.DNF` φ with φ.length ≤ s and `satSet φ` nonempty; reason: contradictory terms evaluate to false and can be dropped, so the class is the same
--   - encoding: fair random bits, with no additional input in the random-bit supply → HaltsWithin includes CoinsInBounds: every readCoin address is below the supplied tape length; reason: the RAM sentinel must not reveal the externally chosen resource bound; this also makes sampler behavior depend only on its output-word input and fair bits
--   - encoding: outputs a PTF of polynomial size → every run outputs a decodable expression of size at most B; only accuracy and nonemptiness are probabilistic; reason: restores the unconditional output clause of Theorem 1.2
--   - encoding: a polynomial expression for the returned real polynomial → PolyExpr uses rational constants, including bit lengths in size; reason: the constructive expressions in Appendix A and the combination on PDF 31 use rational coefficients; these are real polynomials, with polynomial bit length
-- source:
--   Zelin Li, Learning DNF from Satisfying Assignments with Membership Queries, STOC 2027 submission (manuscript sha256 2e246dc4…2670), Theorem 1.2 and Problem 1.1, p. 2 (PDF 3)

import Mathlib
import Definitions.Def_DNFSatMQ_Main_Machine
open TargetedSamplers

namespace DNFSatMQ.Main

/-- Theorem 1.2 (p. 2) with every clause of Problem 1.1: one learner program `PL`, one sampler
program `PS` and one constant `c`, fixed before the input; `poly(n, s, 1/ε)` is
`c (n + s + ⌈1/ε⌉)^c`, used as the learning time, the sampler's number of random bits, the
sampler's time per sample, and the size bound of the PTF. -/
theorem theorem_1_2 :
    ∃ (PL PS : Program) (c : ℕ),
      ∀ (n s : ℕ), 1 ≤ n → 1 ≤ s → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
        ∀ φ : SamplingAC0.DNF (Fin n), φ.length ≤ s → ∀ hF : (satSet φ).Nonempty,
          SolvesP11 ptfHyp PL PS
            (c * (n + s + ⌈1 / ε⌉₊) ^ c) (c * (n + s + ⌈1 / ε⌉₊) ^ c)
            (c * (n + s + ⌈1 / ε⌉₊) ^ c) (c * (n + s + ⌈1 / ε⌉₊) ^ c) n s ε φ hF := by sorry

end DNFSatMQ.Main
