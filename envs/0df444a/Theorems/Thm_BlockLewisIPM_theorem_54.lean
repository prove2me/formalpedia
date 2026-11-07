-- Prove2me | Theorems.Thm_BlockLewisIPM_theorem_54
-- name    : BlockLewisIPM.theorem_54
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:49:36.282196+00:00
-- url     : https://prove2.me/theorems/20b98e7b-318f-4d7f-b002-d739121f9ba5
-- title:
--   Theorem 54 — one program solves linear optimization over a product of convex sets in time $\tilde O(nd+d^{5/2})$ (corrected: strictly feasible point with inner radius $1/\kappa$; $d\ge1$)
-- statement:
--   Let $A\in\mathbb R^{n\times d}$, $b\in\mathbb R^d$, $c\in\mathbb R^n$, and let $K_1,\dots,K_m$ be convex compact sets with $K_i\subset\mathbb R^{n_i}$ and $\sum_in_i=n$, each with a $1$-self-concordant barrier $\phi_i$, accessible through constant-time oracles for the value, gradient and Hessian of $\phi_i$ and the value and gradient of $\phi_i^*$.
--
--   For every $e>0$ there are one program $P$ of the randomized real RAM with these oracles, with rational literals, and constants $C>0$, $k\in\mathbb N$ such that the following holds for every such instance with $d\ge1$, every $\kappa>0$ with $K_i\subseteq B(0,\kappa)$, $\|c_i\|_2\le\kappa$, $\|A_i\|_{\mathrm{op}}\le\kappa$ and a feasible point $z$ with $B(z_i,1/\kappa)\subseteq K_i$, and every $\delta>0$. With probability at least $1-(n+2)^{-e}$, the program, given $A,b,c,\delta$, halts within
--
--   $$C\,n_{\max}^k\,\bigl(nd+d^{5/2}\bigr)\,\bigl(\log(n+d+\kappa+1/\delta+2)\bigr)^k$$
--
--   charged steps and outputs $x$ with
--
--   $$x\in K,\qquad A^\top x=b,\qquad c^\top x\le\min_{y\in K,\,A^\top y=b}c^\top y+\delta .$$
--
--   This matches the fastest known running time for scalar linear programs, for general constant-dimensional blocks with black-box barriers.
--
--   Differences from the source:
--   - correction: no feasibility hypothesis → a point z with A⊤z = b and B(z_i, 1/κ) ⊆ K_i, with log κ in the time; reason: the printed statement fails on m = n = d = 1, K₁ = [−1,1], ϕ₁ = −log(1 − x²), A = (1), b = 2, c = 0, which has no feasible x
--   - correction: d ≥ 0 → d ≥ 1; reason: at d = 0 the bound nd + d^{5/2} is 0 while every run costs at least one step
--   - reading: Õ(·) hides logarithmic terms and the polynomial of block size → C n_max^k · (log(n + d + κ + 1/δ + 2))^k with C, k before the instance; reason: the proof's δ′ depends on R, L, M and δ; κ bounds them all (R1)
--   - reading: no probability printed → failure ≤ (n + 2)^{−e} for every e > 0, on one event for halting, time and output; reason: §3.1: w.h.p.; the constants scale (R2)
--   - reading: "in time", "constant-time oracle access" → one finite program of a real RAM with √, exp, log, a Gaussian tape, rational literals, and charges (1 + n_i)² and 1 + n_i per oracle call; a primal query outside int K_i faults; reason: no model is printed (R3, R4, R5)
--   - reading: for any δ there exists an algorithm → one program with δ as input; reason: the stronger reading
--   - reading: input not listed → κ, K_i, z are not in memory; reason: the input is A, b, c, δ and the oracles (R9)
--   - reading: 1-self-concordant barrier, Definition 2 → the published IsNuSelfConcordantBarrier with ν = 1, which adds the blow-up at the boundary; reason: the word "barrier", §2.1 and Lemma 3 need it (R6)
--   - reading: min over the feasible set → ∀ feasible y, c⊤x ≤ δ + c⊤y; reason: no junk value of sInf (R7)
--   - encoding: blocks of any size, m unrestricted → m ≥ 1, n_i ≥ 1, consecutive numbering in memory; reason: at m = 0 the bound vanishes; an empty block is no constraint (R8)
-- source:
--   Zhang, Wright, A Fast Lewis-weight Interior Point Method for Linear Optimization over Product-Domain (manuscript, sha256 66072000…), Theorem 54, p.49 (= Theorem 1, p.2)

import Mathlib
import Definitions.Def_BlockLewisIPM_Machine

open MeasureTheory

namespace BlockLewisIPM

/-- **Theorem 54** (restated main theorem), p.49 (corrected: C1, C2). Zhang, Wright, *A Fast Lewis-weight
Interior Point Method for Linear Optimization over Product-Domain* (manuscript, sha256 66072000…).

**Formalization Note.** One program, with `C` and `k`, is chosen before the instance, and takes `δ` as
input (the strong reading of "for any `δ > 0`, there exists an algorithm"). `κ` is not an input. C1: a
feasible `z` with `B(z_i, 1/κ) ⊆ K_i`; as printed the theorem fails on the infeasible `K₁ = [-1,1]`, `A = (1)`,
`b = 2`. C2: `d ≥ 1`. Failure is `(n + 2)^{-e}` for every `e > 0` on one event for halting, time and output
(reading R2), on the outer measure. `min` is read as `∀` feasible `y` (reading R7). -/
theorem theorem_54 : ∀ e : ℝ, 0 < e →
    ∃ P : Program, Admissible P ∧ ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (m : ℕ) (I : Instance (Fin m)), I.IsAdmissible → ∀ κ δ : ℝ, I.RadiusBound κ → 0 < δ →
        tape {ω | ¬ I.Success P δ κ C k ω} ≤ ENNReal.ofReal (((I.n : ℝ) + 2) ^ (-e)) := by sorry

end BlockLewisIPM
