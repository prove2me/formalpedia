-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_decremental_sssp_almost_linear
-- name    : DecrAlmostLinearSSSP.Decremental.decremental_sssp_almost_linear
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:55:29.93979+00:00
-- url     : https://prove2.me/theorems/4b8a7998-5dc4-4774-a4cd-232309de9d09
-- title:
--   Theorem 1.1 — Deterministic almost-linear decremental SSSP
-- statement:
--   There exist one deterministic online arithmetic-RAM program, an absolute constant $C>0$, a positive subpolynomial function $a(m)$ and a uniform constant query bound $B$, all chosen before the input. For every finite nonempty directed graph with a fixed source $s$, at most $m$ original edges and $n\le m$ vertices, positive integer weights in $[1,W]$ for arbitrary integer $W\ge1$, and every real $0<\epsilon\le1$, the program handles every legal online sequence of edge deletions. At initialization and after each completed update,
--
--   $$d_G(s,v)\le D(v)\le(1+\epsilon)d_G(s,v)\quad\text{simultaneously for all }v,$$
--   $$\operatorname{work}\le Cma(m)\epsilon^{-1}\max(1,\log_2 W),\qquad\frac{\log a(m)}{\log\max(2,m)}\longrightarrow0.$$
--
--   The program explicitly stores $D$, has $D(s)=0$, and returns $\infty$ exactly at unreachable vertices. Every initialization and maintenance call terminates, and a read-only query returns the stored flag and value in at most $B$ instructions. Total work includes initialization, repairs, all interface operations, report processing, refreshes, writes and the general-domain adapters. The program sees only the initial input and past deletions. Disconnected initial graphs, incoming source edges, empty streams, singleton vertex sets, $W=1$ and arbitrarily small real accuracy are included. No decremental path-reporting assertion is made.
--
--   The logarithm is saturated at $W=1$ because explicitly maintained outputs require positive work even on unweighted graphs. The result is the full Theorem 1.1 target, not the polynomial-weight internal theorem or a distance certificate alone.
--
--   Differences from the source:
--   - reading: Theorem 1.1 leaves its computation model unnamed → a deterministic unit-cost scalar arithmetic RAM with charged memory access, comparisons, arithmetic and logarithms; reason: the companion Lemma 4.1 names unit-cost arithmetic; no bit-complexity or arbitrary-function oracle is claimed
--   - reading: the printed total bound contains log W, including W=1 in its graph domain → the factor is max(1,log₂ W); reason: on a unit-weight directed n-cycle with n≥3, deleting the source outgoing edge forces finite outputs to become infinity, so the literal log 1=0 budget is impossible; footnote 1 uses a positive scale count
--   - encoding: a finite directed graph and explicitly maintained approximate distances under edge deletions → integer-indexed vertices and edge identifiers, extended nonnegative distances, scalar flag/value storage and finite instruction runs; reason: this changes no admitted graph, accuracy or legal stream; initialization, each prefix and queries have operational work counts and future updates are absent from the input
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #912 (October 2026), p. 3, Theorem 1.1; p. 1, abstract (domain, explicit output, constant queries and exact unreachability); p. 4, general-domain reduction and footnote 1; pinned PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf

import Mathlib
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Adapters

set_option autoImplicit false
open scoped ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental

/-- Theorem 1.1: one deterministic online program, chosen uniformly before all input
parameters, and actual charged executions for initialization and every legal deletion prefix. -/
theorem decremental_sssp_almost_linear :
    ∃ (p : Program) (C : ℝ) (a : ℕ → ℝ) (queryBound : ℕ),
      0 < C ∧ 0 < queryBound ∧ Subpolynomial a ∧
      ∀ i : Input, i.Valid → Maintains p C a queryBound true i := by sorry

end DecrAlmostLinearSSSP.Decremental
