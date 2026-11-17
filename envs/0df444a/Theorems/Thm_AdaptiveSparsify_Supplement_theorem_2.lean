-- Prove2me | Theorems.Thm_AdaptiveSparsify_Supplement_theorem_2
-- name    : AdaptiveSparsify.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:53:21.898673+00:00
-- url     : https://prove2.me/theorems/5504f369-c48c-490d-a529-6c2bf98fe9ca
-- title:
--   Theorem 2 (corrected: C1, C2 of Theorem 1) — general block sizes in time $\tilde O\big(nd+M^4\nu(M^{\omega-1}+d)+\sqrt{\nu M}(d^6+\sum_{i\in L}(n_i+d)^\omega)\big)$
-- statement:
--   For every $c>0$ and every achievable matrix multiplication exponent $\omega_0\ge2$ there are one admissible program $P$ of the randomized barrier-oracle RAM and constants $C>0$, $k\in\mathbb N$ such that the following holds. Let
--
--   $$\min_{x\in K_1\times\cdots\times K_m,\ A^\top x=b}c^\top x$$
--
--   be an ERM instance with $A\in\mathbb R^{n\times d}$ satisfying every hypothesis of Theorem 1 except the bound $n_i\le C_K$:
--
--   1. each $K_i\subseteq[-\kappa,\kappa]^{n_i}$ is compact and convex, $n_i\ge1$, and $K_i$ is given by a $\nu_i$-self-concordant barrier;
--   2. $A,b,c$ have entries at most $\kappa$ and $A^\top A\succeq\kappa^{-1}I$, with $d\ge1$;
--   3. there is a feasible $z$ with $B(z_i,1/\kappa)\subseteq K_i$ for all $i$, and start points $w_i$ with $B(w_i,1/\kappa)\subseteq K_i$ are given.
--
--   Let $L\subseteq[m]$ be any set of blocks, let $M\ge1$ satisfy $n_i\le M$ for all $i\notin L$, and let $\nu=\sum_{i}\nu_i$, $\nu_{\max}=\max_i\nu_i$. Then for every $\varepsilon>0$, given $L$ and $\nu_1,\dots,\nu_m$, with probability at least $1-(n+2)^{-c}$ the run of $P$ halts within
--
--   $$C\Big(nd+M^4\nu\big(M^{\omega_0-1}+d\big)+\sqrt{\nu M}\Big(d^6+\sum_{i\in L}(n_i+d)^{\omega_0}\Big)\Big)\big(\log(n+d+\kappa+1/\varepsilon+\nu_{\max}+2)\big)^k$$
--
--   units of work and outputs $x$ with $x_i\in K_i$ for all $i$, $A^\top x=b$, and $c^\top x\le\varepsilon+c^\top y$ for every feasible $y$.
--
--   Theorem 1 is the case $L=\emptyset$, $M=C_K$, $\nu=O(n)$; carrying a large block exactly (a set $L$ with one block of dimension $d^2+1$) is what the minimum volume enclosing ellipsoid algorithm of Section 7 uses.
--
--   **Formalization Note** "Achievable" means that some admissible program of the same machine multiplies two $N\times N$ real matrices within $C_\omega N^{\omega_0}$ work for every $N\ge1$; the program and constants may depend on $\omega_0$, $C_\omega$ and that multiplication program.
--
--   Differences from the source:
--   - correction: the hypotheses of Theorem 1 as printed (no feasibility assumption, no start point) → the published hypotheses with C1 (a feasible z with B(z_i,1/κ) ⊆ K_i) and C2 (given w_i with B(w_i,1/κ) ⊆ K_i); reason: Theorem 1's printed form is false (base mission C1: m = n = d = 1, K₁ = [0,1], φ₁ = −log x − log(1−x), ν₁ = 2, A = (1), b = 2, c = 0, κ = 2, L = ∅, M = 1 meets every printed hypothesis of Theorem 2 and no feasible x exists); C2 because the barrier oracle answers only on int K_i, as in the base mission
--   - reading: an x "can be computed" (by the randomized algorithm of Theorem 1) → failure at most (n + 2)^{−c} for every c > 0, on one event for halting, time and the three output clauses, bounded in outer measure; reason: reading R2 of the base mission: the proof is with high probability (Lemmas 4.13, 4.15, 5.5–5.7) with constants that scale; base n + 2 avoids a vacuous bound at n = 1
--   - reading: "an algorithm" → one finite admissible program of the published barrier-oracle RAM AdaptiveSparsify.Machine (rational literals, + − × ÷, √, exp, Gaussian tape, oracle charged (1 + n_i)², unit cost); reason: readings R3–R5 of the base mission, unchanged
--   - reading: ω, the matrix multiplication exponent → every ω₀ ≥ 2 achievable on the machine (IsMatMulProgram with constant C_ω); the program and constants may depend on ω₀, C_ω and the multiplication program; reason: ω is an infimum that need not be attained; ω₀ = 3 is achievable, and any faster multiplication program on the machine gives the theorem with its exponent
--   - reading: Õ hides logs of n, d, κ, 1/ε and max_i ν_i → explicit C, k chosen after c and ω₀ and before the instance, ν, L, M and ε, with the factor (log(n + d + κ + 1/ε + ν_max + 2))^k and no other hidden factor; reason: reading R1 of the base mission; there is no C_K in Theorem 2
--   - reading: block i has a ν_i-self-concordant barrier; L is any set of blocks → ν_1, …, ν_m and the indicator of L are part of the input (real cells after ε, integer cells 3 + m + i); M is not an input; reason: the step size η = εα/(C_center √ν) of §6.4 (p.46) needs ν, and L is chosen by the user; M enters only the time bound, which is increasing in M, so withholding it only strengthens the statement
--   - encoding: coordinate sets S_i, the minimum of c⊤x, Definition 3.1 → consecutive blocks with n_i ≥ 1 and d ≥ 1, c⊤x ≤ ε + c⊤y for every feasible y, the published IsNuSelfConcordantBarrier with parameter ν_i; reason: readings R7–R9 of the base mission, unchanged
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Theorem 2, p.7; proof §6.4, pp.45–47

import Mathlib
import Definitions.Def_AdaptiveSparsify_Supplement_MatMul
import Definitions.Def_AdaptiveSparsify_Supplement_GeneralBlocks

open Matrix

namespace AdaptiveSparsify

namespace Supplement

/-- **Theorem 2** (General block sizes), p.7; proof in §6.4, pp.45–47.

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…), Theorem 2, p.7.

"Consider an instance of (2) satisfying the hypotheses of Theorem 1 except for the bound n_i ≤ C_K,
where block i has dimension n_i and a ν_i-self-concordant barrier. Let L ⊆ [m] be any set of blocks,
let M ≥ 1 satisfy n_i ≤ M for all i ∉ L, and let ν = ∑_{i∈[m]} ν_i. Then an x as in Theorem 1 can
be computed in time Õ(nd + M⁴ν(M^{ω−1} + d) + √(νM)(d⁶ + ∑_{i∈L}(n_i + d)^ω)), where Õ hides logs of
n, d, κ, 1/ε, and max_i ν_i."

**Formalization Note.** The machine is the barrier-oracle RAM `AdaptiveSparsify.Machine` (readings
R3–R5 of the base mission). `ω` is read as any exponent `ω₀ ≥ 2` achievable on that machine
(`IsMatMulProgram`); the program and the constants may depend on `ω₀`, `C_ω`, the multiplication
program and the failure exponent `c`, and on nothing else: they are chosen before the instance, `ν`,
`L`, `M` and `ε`. The program reads `L` and `ν` from memory (`generalIntMem`, `generalRealMem`).
Halting, time and the three output clauses hold on one event of probability at least
`1 - (n + 2)^{-c}` (reading R2), bounded in outer measure. `GeneralAdmissible` keeps corrections C1
and C2 of Theorem 1. -/
theorem theorem_2 : ∀ c : ℝ, 0 < c →
    ∀ (ω₀ Cω : ℝ) (Pmul : Program), 2 ≤ ω₀ → Supplement.IsMatMulProgram Pmul ω₀ Cω →
    ∃ P : Program, Admissible P ∧ ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (I : ERMInstance) (ν : Fin I.blocks.m → ℝ) (L : Finset (Fin I.blocks.m)) (M : ℝ),
        Supplement.GeneralAdmissible I ν → 1 ≤ M → (∀ i, i ∉ L → (I.blocks.dim i : ℝ) ≤ M) →
        ∀ ε : ℝ, 0 < ε →
          tape {ω | ¬ Supplement.GeneralSuccess P I ν L M ε ω₀ C k ω} ≤
            ENNReal.ofReal (((I.blocks.n : ℝ) + 2) ^ (-c)) := by sorry

end Supplement

end AdaptiveSparsify
