-- Prove2me | Theorems.Thm_AdaptiveSparsify_theorem_1
-- name    : AdaptiveSparsify.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:46:16.511655+00:00
-- url     : https://prove2.me/theorems/adcd8f48-8b18-430e-a44e-d3f32930bdb9
-- title:
--   Theorem 1 (corrected: adds a strictly feasible point and start points) — ERM solved to accuracy $\varepsilon$ in time $\tilde O(nd+d^6\sqrt n)$
-- statement:
--   For every $C_K\ge1$ and $c>0$ there are one admissible program $P$ of the randomized barrier-oracle RAM and constants $C>0$, $k\in\mathbb N$ such that the following holds. Let
--
--   $$\min_{x\in K_1\times\cdots\times K_m,\ A^\top x=b}c^\top x$$
--
--   be an ERM instance with $A\in\mathbb R^{n\times d}$, in which:
--
--   1. each $K_i\subseteq[-\kappa,\kappa]^{n_i}$ is compact and convex, $1\le n_i\le C_K$, and $K_i$ is given by a $C_K$-self-concordant barrier;
--   2. $A,b,c$ have entries at most $\kappa$ and $A^\top A\succeq\kappa^{-1}I$, with $d\ge1$;
--   3. there is a feasible $z$ with $B(z_i,1/\kappa)\subseteq K_i$ for all $i$;
--   4. start points $w_i$ with $B(w_i,1/\kappa)\subseteq K_i$ are given.
--
--   Then for every $\varepsilon>0$, with probability at least $1-(n+2)^{-c}$ over the Gaussian tape, the run of $P$ halts within
--
--   $$C\,(nd+d^6\sqrt n)\,\big(\log(n+d+\kappa+1/\varepsilon+2)\big)^k$$
--
--   units of work and outputs $x$ with $x_i\in K_i$ for all $i$, $A^\top x=b$, and $c^\top x\le\varepsilon+c^\top y$ for every feasible $y$.
--
--   The bound is nearly linear in the input size when $A$ is dense and $n\ge d^{10}$; the minimum enclosing ball problem is one application.
--
--   Differences from the source:
--   - correction: no assumption on feasibility → there is z with A⊤z = b and B(z_i, 1/κ) ⊆ K_i (a larger κ covers any radius); reason: as printed the theorem is false: m = n = d = 1, K₁ = [0,1], φ₁ = −log x − log(1−x), A = (1), b = 2, c = 0, κ = 2 meets every printed hypothesis and no x satisfies the conclusion; the proof needs a strictly feasible start (p.44)
--   - correction: no start point → given w_i with B(w_i, 1/κ) ⊆ K_i; reason: the barrier oracle answers only on int K_i (p.6, Definition 3.1): with K₂ = [0,1] with its log barrier, A = (0,1)⊤, b = 1/2, c = 0, and K₁ = [u, u + 1/κ] for u on a grid of about κ² positions, polylog(κ) queries miss K₁ with probability → 1, and the proof starts from [LSZ19, Lemma D.2], which needs an interior point
--   - reading: a self-concordant barrier, with its parameter unstated → each ν_i ≤ C_K; reason: reading R6: stated in Appendix C (p.70), §6.4 (p.45), and "Theorem 1 is the case … ν = O(n)" (p.7)
--   - reading: Õ hides factors of C_K and logs of n, d, κ, 1/ε → explicit C, k, chosen after C_K and c and before the instance and ε, with (log(n + d + κ + 1/ε + 2))^k; reason: reading R1: C_K is an absolute constant, so C, k and P may depend on it and on no instance
--   - reading: no probability printed → failure at most (n + 2)^{−c} for every c > 0, on one event for halting, time and all output clauses, bounded in outer measure; reason: reading R2: the proof gives 1 − n^{−Ω(1)} with constants that scale; base n + 2 avoids a vacuous bound at n = 1
--   - reading: "an algorithm" in "total time" → one finite admissible program of the barrier-oracle RAM: rational literals, + − × ÷, √, exp, integer pointers, Gaussian tape, oracle charged (1 + n_i)², unit cost; reason: readings R3–R5: the arithmetic the paper's method needs, and no matrix, log or floor instruction
--   - reading: oracle for the barrier on int K_i → a query outside int K_i faults and the run fails; reason: reading R5: Definition 3.1 defines the barrier on int K only, so no membership information leaks
--   - encoding: the minimum of c⊤x over feasible points → c⊤x ≤ ε + c⊤y for every feasible y; reason: reading R7: same meaning when the feasible set is nonempty and compact, without an infimum junk value
--   - encoding: coordinate sets S_i → consecutive blocks with n_i ≥ 1, d ≥ 1; reason: reading R8: a permutation of rows of A and c maps one to the other; at d = 0 the time bound would be 0
--   - encoding: Definition 3.1, p.12 → the published IsNuSelfConcordantBarrier; reason: reading R9: the line form, equal to items 1–3 by polarization, and with no inverse of a possibly singular Hessian
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Theorem 1, pp.6–7

import Mathlib
import Definitions.Def_AdaptiveSparsify_ERMInstance

open Matrix

namespace AdaptiveSparsify

/-- **Theorem 1**, pp.6–7 (corrected: C1, C2).

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…), Theorem 1, pp.6–7.

"There is an algorithm that takes an ERM instance as in (2) such that: 1. each K_i is given by
self-concordant barriers, bounded by κ in magnitude K_i ⊆ [−κ, κ]^{n_i}, and n_i ≤ C_K for some
absolute constant C_K, 2. A, b, c have entries at most κ, and A has minimum singular value at least
κ^{−1/2} (A⊤A ⪰ κ⁻¹I), outputs x such that x ∈ K_1 × ··· × K_m, A⊤x = b, and c⊤x ≤ ε + min c⊤x in
total time Õ(nd + d⁶√n), where Õ hides factors of C_K, as well as logs of n, d, κ, and 1/ε."

**Formalization Note.** One program `P` and the constants `C`, `k` are chosen before the instance
and `ε`, and may depend on `C_K` and the failure exponent `c` (readings R1, R2). The machine is the
barrier-oracle RAM of `AdaptiveSparsify.Machine` (readings R3–R5). Halting, time and the three output
clauses hold on one event of probability at least `1 - (n + 2)^{-c}`, bounded in outer measure.
`IsAdmissible` adds the strictly feasible point (C1) and the start points (C2). -/
theorem theorem_1 : ∀ CK : ℕ, 1 ≤ CK → ∀ c : ℝ, 0 < c →
    ∃ P : Program, Admissible P ∧ ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ I : ERMInstance, I.IsAdmissible CK → ∀ ε : ℝ, 0 < ε →
        tape {ω | ¬ ERMInstance.Success P I ε C k ω} ≤
          ENNReal.ofReal (((I.blocks.n : ℝ) + 2) ^ (-c)) := by sorry

end AdaptiveSparsify
