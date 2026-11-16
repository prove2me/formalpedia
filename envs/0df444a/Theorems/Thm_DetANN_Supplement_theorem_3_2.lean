-- Prove2me | Theorems.Thm_DetANN_Supplement_theorem_3_2
-- name    : DetANN.Supplement.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:18:18.214797+00:00
-- url     : https://prove2.me/theorems/7cef0c6f-fed1-40f1-8185-3f91b93b8058
-- title:
--   Theorem 3.2, p.7 — a $\tau$-balanced block system with $b=O(\tau^{-2}\log n)$, constructed deterministically in $\mathrm{poly}(n,d,1/\tau)$ operations and evaluated in $O(bd\log n)$ time
-- statement:
--   Let $d\ge1$ be a power of two, $n\ge d$, and let $P=\{P_0,\dots,P_{n-1}\}\subseteq\mathbb R^d$ be $n$ distinct points. A $\tau$-balanced block system for $P$ (Definition 3.1) consists of linear maps $A_1,\dots,A_d:\mathbb R^d\to\mathbb R^b$ with
--
--   $$\sum_{i=1}^d\|A_iz\|_2^2=\|z\|_2^2\quad(z\in\mathbb R^d),\qquad \frac{1-\tau}{d}\|x-y\|_2^2\le\|A_i(x-y)\|_2^2\le\frac{1+\tau}{d}\|x-y\|_2^2\quad(x,y\in P,\ i\in[d]).$$
--
--   **Theorem.** There are two fully deterministic real-RAM programs, a construction program $\mathrm{Pre}$ and an evaluation program $\mathrm{Ev}$, and constants $C,K\in\mathbb N$ such that for all such $d,n,P$ and every $\tau\in(0,1)$:
--
--   1. $\mathrm{Pre}$, given $P$ and $\tau$, halts within $C\,(nd/\tau)^K$ steps and constructs a $\tau$-balanced block system for $P$ with block dimension
--   $$b\le C\,\tau^{-2}\,(1+\log n);$$
--   2. after this preprocessing, $\mathrm{Ev}$ computes $A_1z,\dots,A_dz$ for every vector $z\in\mathbb R^d$ within $C\,b\,d\,(1+\log n)$ steps.
--
--   "Constructs" and "computes" are in the sense of the block-construction semantics `DetANN.Supplement.BlockConstruction`: the maps are those whose coordinates the evaluation program outputs. The same programs and constants serve every $d$, $n$, $P$ and $\tau$.
--
--   This is the dimension-reduction primitive of the paper: it supplies the blocks on which both the exhaustive construction (§4) and the expander construction (§7) build their low-dimensional nearest-neighbor structures.
--
--   **Formalization Note** The machine is the published `PNormReg.Machine` restricted to deterministic programs (no coin, no real power, rational literals), with the input layout and second-program start state of `DetANN.DataStructure`. The point set is an injective list $P:\mathrm{Fin}\,n\to\mathbb R^d$.
--
--   Differences from the source:
--   - reading: "one can deterministically construct … arithmetic operations … time" (no machine named) → one pair of deterministic programs on the published real RAM, time = executed instructions, the maps being those output by the evaluation program; reason: the paper names no machine; each instruction does at most one arithmetic operation, so a step bound is at least as strong as an operation bound.
--   - encoding: $b=O(\tau^{-2}\log n)$ and $O(bd\log n)$ → $b\le C\tau^{-2}(1+\log n)$ and $\le C\,b\,d\,(1+\log n)$ with $C$ fixed before the instance; reason: identical for $n\ge2$; at $n=1$ the literal $\log n=0$ would force $b=0$, which Parseval (8) forbids for $d\ge1$.
--   - encoding: $\mathrm{poly}(n,d,1/\tau)$ → $C\,(nd/\tau)^K$ with $C,K$ fixed before the instance; reason: $nd/\tau\ge1$, so every polynomial in $n,d,1/\tau$ is bounded by such an expression.
--   - encoding: $P\subseteq\mathbb R^d$ of size $n$ → injective $P:\mathrm{Fin}\,n\to\mathbb R^d$, given in the input layout; reason: Lean convention for an input list of $n$ distinct points.
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), Theorem 3.2, p.7 (PDF p.7); standing assumptions §3, p.7; Definition 3.1, p.7; proof in §6, pp.14–16

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_Supplement_BlockConstruction

namespace DetANN

namespace Supplement

/-- **Theorem 3.2** (Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High
Dimensions*, STOC 2027 submission (manuscript sha256 96f0ad57…), p.7).
Given `P ⊆ ℝ^d` and `τ ∈ (0, 1)`, one can deterministically construct a `τ`-balanced block system with
`b = O(τ^{−2} log n)`. The construction takes `poly(n, d, 1/τ)` arithmetic operations. After
preprocessing, all `d` maps can be evaluated on a vector in `O(b d log n)` time.

**Formalization Note.** One pair of deterministic programs `Pre` (construction) and `Ev`
(evaluation) and constants `C, K` serve every instance: they are chosen before `d`, `n`, the points
and `τ` (`τ` is an input of `Pre`, in real cell `0`). The paper's standing assumptions (§3, p.7) are
kept: `d` a power of two (hence `d ≥ 1`), `n ≥ d`, and `n` distinct points (`P` injective).
`poly(n, d, 1/τ)` is `C·(n·d/τ)^K`, equivalent since `n·d/τ ≥ 1`; `log n` is read as `1 + log n`
(natural log) in both the bound on `b` and the evaluation time, which avoids `log 1 = 0` at `n = 1` and
changes nothing for `n ≥ 2`. Construction and evaluation semantics are those of
`DetANN.Supplement.IsBlockConstruction`. -/
theorem theorem_3_2 :
    ∃ Pre Ev : PNormReg.Program, DetProgram Pre ∧ DetProgram Ev ∧
      ∃ C K : ℕ, ∀ d n : ℕ, (∃ k : ℕ, d = 2 ^ k) → d ≤ n →
        ∀ P : Fin n → EuclideanSpace ℝ (Fin d), Function.Injective P →
          ∀ τ : ℝ, 0 < τ → τ < 1 →
            IsBlockConstruction Pre Ev P τ
              ((C : ℝ) * ((n : ℝ) * d / τ) ^ K)
              ((C : ℝ) * τ⁻¹ ^ 2 * (1 + Real.log n))
              (fun b => (C : ℝ) * b * d * (1 + Real.log n)) := by sorry

end Supplement

end DetANN
