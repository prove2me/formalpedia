-- Prove2me | Theorems.Thm_EuclidKSteiner_theorem_1_1
-- name    : EuclidKSteiner.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:16:18.989626+00:00
-- url     : https://prove2.me/theorems/fd5bbbc1-baa0-40f9-aaa4-6ffc3d5bcd3a
-- title:
--   Theorem 1.1 (Main result) — Discrete Euclidean $k$-Steiner Tree in $2^{O(k\log k)}n^{O(1)}$ time in every fixed dimension
-- statement:
--   There is an exponent $c$ such that for every dimension $d$ there are a deterministic real-RAM program and a constant $C>0$ with the following property. For every budget $k\ge0$ and every instance with terminals $P_0,\dots,P_{n_P-1}$ and candidates $Q_0,\dots,Q_{n_Q-1}$ in $\mathbb R^d$ with arbitrary real coordinates, the program halts within
--   $$C\cdot2^{C\,k\log_2(k+2)}\cdot(n_P+n_Q+2)^c$$
--   steps and outputs a set $S$ of at most $k$ distinct candidate indices such that
--   $$w\bigl(\mathrm{MST}(P\cup S)\bigr)\le w\bigl(\mathrm{MST}(P\cup S')\bigr)\quad\text{for every }S'\subseteq Q\text{ with }|S'|\le k .$$
--
--   The machine is the real RAM with unit-time arithmetic, comparisons and square roots. The theorem shows that Discrete Euclidean $k$-Steiner Tree, which has an obvious $n^{O(k)}$ algorithm, is fixed-parameter tractable in the number $k$ of Steiner points in every fixed dimension, with an exponent of $n$ independent of $d$.
--
--   **Formalization Note** The machine is the published real RAM `MatMulTimeLP.RealRAM` restricted to admissible programs (`FewInnerTSP.Admissible`: rational literals, no random draws, square roots allowed); every executed instruction costs one step and there is no floor. Without draws the run does not depend on the random tape. The input is $k,n_P,n_Q$ followed by the coordinates; the output is $|S|$ followed by the indices.
--
--   Differences from the source:
--   - reading: the real-RAM model, with unit-time arithmetic, comparisons, and square roots → the published real RAM MatMulTimeLP.RealRAM restricted by FewInnerTSP.Admissible: rational literals, no random draws, rsqrt allowed, every executed instruction (index bookkeeping and input reads included) costing 1, no floor; reason: the page names no instruction set; under an existential program the fewest primitives give the strongest statement
--   - reading: for every fixed dimension, 2^{O(k log k)} n^{O(1)} time → ∃ c, ∀ d, ∃ program, ∃ C > 0, ∀ instance: t + 1 ≤ C·2^{C·k·log₂(k+2)}·(nP + nQ + 2)^c; reason: the abstract writes 2^{O_d(k log k)}n^{O(1)}, so only the first constant depends on d; this is the stronger reading; k log₂(k+2) replaces k log k, which vanishes at k = 1; +2 keeps the base at least 2
--   - encoding: find a set S ⊆ Q with |S| ≤ k minimizing w(MST(P ∪ S)) → the output cells hold |S| and the distinct indices of S, |S| ≤ k, and mstWeight(P ∪ S) ≤ mstWeight(P ∪ S') for every S' ⊆ Q with |S'| ≤ k; reason: a machine statement needs an output layout; the task asks for S itself
--   - encoding: solved deterministically → the conclusion holds on every random tape; admissible programs have no draws; reason: the machine is deterministic on admissible programs
--   - generalization: a terminal set P ⊆ ℝ^d and a candidate set Q ⊆ ℝ^d, n = |P| + |Q| → indexed sequences P : Fin nP → ℝ^d, Q : Fin nQ → ℝ^d with repetitions allowed, the point set of a selection being the image, n = nP + nQ; reason: sets are the injective case, where nP + nQ = |P| + |Q|
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), Theorem 1.1, p.2 (PDF p.4); problem statement §1, p.1 (PDF p.3); real-RAM model p.3 (PDF p.5)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_FewInnerTSP_Admissible
import Definitions.Def_EuclidKSteiner_Instance

namespace EuclidKSteiner

/-- **Theorem 1.1 (Main result).** Bhore, Kisfaludi-Bak, Marx, Odak, *Parameterized Tractability of
Euclidean k-Steiner Tree*, STOC 2027 submission (manuscript sha256 75361687…), Theorem 1.1, p.2
(PDF p.4): "For every fixed dimension, Discrete Euclidean k-Steiner Tree can be solved
deterministically in 2^{O(k log k)}n^{O(1)} time." (Footnote 1: all logarithms have base 2.)

There is an exponent `c` such that for every dimension `d` there are an admissible real-RAM program
and a constant `C > 0` with the following property. On every instance (budget `k ≥ 0`, terminals
`P 0, …, P (nP−1)` and candidates `Q 0, …, Q (nQ−1)` in `ℝ^d` with arbitrary real coordinates,
`nP, nQ ≥ 0`) and every tape, the run halts at a step `t` with
`t + 1 ≤ C · 2^{C·k·log₂(k+2)} · (nP + nQ + 2)^c` and outputs a list of at most `k` distinct candidate
indices whose selection `S` minimizes `w(MST(P ∪ S))` over all `S' ⊆ Q` with `|S'| ≤ k`.

**Formalization Note**
* Machine: `MatMulTimeLP.RealRAM` restricted by `FewInnerTSP.Admissible` (rational literals, no
  random draws, `rsqrt` allowed): the paper's "real-RAM model, with unit-time arithmetic,
  comparisons, and square roots" (p.3). Every executed instruction costs `1`; there is no floor and
  no real-to-index cast. Without draws the run does not depend on the tape `ω`.
* Quantifiers: `c` before `d` (the exponent of `n` does not depend on the dimension; the abstract
  writes `2^{O_d(k log k)}n^{O(1)}`); the program and `C` after `d` ("for every fixed dimension")
  and before the instance.
* `k·log₂(k+2)` stands for `k log k`: it is positive at `k = 1`, and for `k ≥ 2` the two differ by a
  constant factor. `n + 2` keeps the base at least `2` when `n = 0`.
* The output is the selection `S` itself (cell `m = |S|`, then the 0-based indices), and the
  optimality is against every `S' ⊆ Q` with `|S'| ≤ k`. Repeated input points are allowed; the point
  set of a selection is the image (`selection`). -/
theorem theorem_1_1 :
    ∃ c : ℕ, ∀ d : ℕ, ∃ A : MatMulTimeLP.Program, FewInnerTSP.Admissible A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (k nP nQ : ℕ) (P : Fin nP → E d) (Q : Fin nQ → E d) (ω : MatMulTimeLP.Tape),
      ∃ t : ℕ, MatMulTimeLP.HaltsAt A (layout k P Q) ω t ∧
        (t : ℝ) + 1 ≤ C * (2 : ℝ) ^ (C * k * Real.logb 2 ((k : ℝ) + 2)) * ((nP + nQ : ℝ) + 2) ^ c ∧
        ∃ L : List (Fin nQ), L.Nodup ∧ L.length ≤ k ∧
          OutputIs A (layout k P Q) ω t (encodeIndices L) ∧
          ∀ S' : Finset (Fin nQ), S'.card ≤ k →
            mstWeight (selection P Q L.toFinset) ≤ mstWeight (selection P Q S') := by sorry

end EuclidKSteiner
