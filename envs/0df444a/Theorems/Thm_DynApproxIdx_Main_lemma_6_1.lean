-- Prove2me | Theorems.Thm_DynApproxIdx_Main_lemma_6_1
-- name    : DynApproxIdx.Main.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:53:06.515342+00:00
-- url     : https://prove2.me/theorems/3d20ec04-07ff-4840-9c7a-2296ab835dc1
-- title:
--   Lemma 6.1 — balanced monotone range decomposition in O(kλ·eval_f·log m) time with t ≤ 5kλ intervals
-- statement:
--   Let $k,m,\lambda$ be positive integers with $0<k<m$, and let $f$ be a monotone function from the subintervals of $[0..m)$ to $[0..\lambda]$ with $f(\{i\})=0$ for every $i\in[0..m)$, available as an oracle with evaluation cost $\mathrm{eval}_f$. **Balanced Monotone Range Decomposition** asks for a partition of $[0..m)$ into intervals $I_1,\dots,I_t$ such that
--   $$t>k\quad\text{and}\quad f(I_1)=f(I_2)=\dots=f(I_{k+1})\ge f(I_{k+2})\ge\dots\ge f(I_t),$$
--   together with the value $f(I_1)$. Lemma 6.1 says that it can be solved in $O(k\lambda\cdot\mathrm{eval}_f\cdot\log m)$ time with an output of $t\le5k\lambda$ intervals.
--
--   Precisely: there are one program $P$ of the word RAM, a constant $C$ and a width constant $c_w$ such that for every such input, every word size $w\ge c_w\lceil\log_2(m+\lambda+3)\rceil$ and every coin tape, the machine halts within $C\,k\lambda\log_2 m$ steps and at most $C\,k\lambda\log_2 m$ oracle calls, having written a valid output with $t\le 5k\lambda$.
--
--   The lemma computes the split points of a pattern in the paper's index (§6.3, §7).
--
--   Differences from the source:
--
--   - reading: solved in O(kλ · eval_f · log m) time → one program, universal C and c_w: at most C·k·λ·log₂ m machine steps and at most C·k·λ·log₂ m oracle calls, on every coin tape; reason: time = steps + eval_f·calls; for all eval_f ≥ 1 this is O(kλ·eval_f·log m) iff both counts are O(kλ log m); log₂ m ≥ 1 since m > k ≥ 1
--   - encoding: f computable in eval_f time → f is an oracle on the word RAM DynBrooks_Machine: write 1, l, r, then read f([l..r)); one oracle call per delivery (Oracle); reason: the algorithm may only evaluate f, at the stated cost
--   - encoding: a monotone f from subintervals of [0..m) to integers in [0..λ] with f({i}) = 0 → f : ℕ → ℕ → ℕ with f l r = f([l..r)) constrained on nonempty subintervals l < r ≤ m (IsBMRDInput); reason: the empty interval is never evaluated: partition blocks are nonempty; values are integers in [0..λ], hence naturals
--   - encoding: output: a partition I_1, …, I_t of [0..m) together with f(I_1) → the written words 0, t, l_1, r_1, …, l_t, r_t, v after the queries, then halt; the list of intervals is a partition (each position covered exactly once), in the written order; reason: the order I_1, …, I_t is the one the chain of values refers to
--   - encoding: the machine model (unstated) → the published word RAM DynBrooks_Machine with word size w ≥ c_w ⌈log₂(m + λ + 3)⌉; reason: inputs, interval endpoints, t ≤ 5kλ and values fit in O(log(m + λ))-bit words
-- source:
--   Charalampopoulos, Ellert, Radoszewski, Dynamic Approximate Text Indexing, STOC 2027 submission (manuscript sha256 7f902057…), p. 22 (PDF 24), Lemma 6.1 with the problem box above it

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynApproxIdx_Main_Run
import Definitions.Def_DynApproxIdx_Main_Oracle

namespace DynApproxIdx.Main

/-- **Lemma 6.1** (Charalampopoulos, Ellert, Radoszewski, *Dynamic Approximate Text Indexing*, STOC
2027 submission, p. 22 (PDF 24)), with the problem box above it. Balanced Monotone Range
Decomposition can be solved in `O(kλ · eval_f · log m)` time with an output of `t ≤ 5kλ`
intervals: there are one program `P`, a constant `C` and a width constant `c_w` such that, for all
positive integers `k, m, λ` with `0 < k < m` and every monotone `f` from the subintervals of
`[0..m)` to `[0..λ]` with `f({i}) = 0`, given as an oracle, at every word size
`w ≥ c_w ⌈log₂(m + λ + 3)⌉` and on every coin tape the machine halts within `C·k·λ·log₂ m` steps
and `C·k·λ·log₂ m` oracle calls, having written a partition `I_1, …, I_t` of `[0..m)` with `t > k`,
`f(I_1) = ⋯ = f(I_{k+1}) ≥ f(I_{k+2}) ≥ ⋯ ≥ f(I_t)` and `t ≤ 5kλ`, and the value `f(I_1)`. -/
theorem lemma_6_1 :
    ∃ (P : DynBrooks.Program) (C : ℝ) (cw : ℕ),
      ∀ (k m lam : ℕ) (f : ℕ → ℕ → ℕ), IsBMRDInput k m lam f →
        ∀ w : ℕ, cw * Nat.clog 2 (m + lam + 3) ≤ w → ∀ ω : ℕ → BitVec w,
          ∃ T : ℕ, Halted P (oRun P ω k m lam f T).1 ∧
            (T : ℝ) ≤ C * k * lam * Real.logb 2 m ∧
            ((oRun P ω k m lam f T).2 : ℝ) ≤ C * k * lam * Real.logb 2 m ∧
            BMRDAnswer k m lam f (oRun P ω k m lam f T).1.output := by sorry

end DynApproxIdx.Main
