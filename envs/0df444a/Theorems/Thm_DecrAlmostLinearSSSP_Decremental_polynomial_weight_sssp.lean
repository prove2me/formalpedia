-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_polynomial_weight_sssp
-- name    : DecrAlmostLinearSSSP.Decremental.polynomial_weight_sssp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:55:19.992752+00:00
-- url     : https://prove2.me/theorems/e806e6ce-d7f3-4141-a950-5395987d05ab
-- title:
--   Theorem 3.1 — Polynomial-weight decremental SSSP
-- statement:
--   For every fixed polynomial exponent $c$, there exist a deterministic online program, constants $C>0$ and $B>0$ and a positive subpolynomial overhead $a(m)$, chosen before graph and accuracy instances. For every directed graph with $m\ge n\ge2$, at most $m$ original edges, integer weights in $[1,W]$ with $W\le m^c$, a fixed source and $1/m<\epsilon<1$, every legal deletion stream is maintained with simultaneous estimates
--
--   $$d_G(s,v)\le D(v)\le(1+\epsilon)d_G(s,v),\qquad\operatorname{work}\le Cma(m)\epsilon^{-1}.$$
--
--   Initialization and every completed update terminate, the source entry is zero, unreachable vertices are identified exactly, and stored-array queries use at most $B$ instructions. Initial disconnection and source-incoming edges are handled internally.
--
--   The source's proof also yields an explicit toggle budget for every attained core prefix:
--
--   $$T\le16K^3Am\log(2Q).$$
--
--   The factor $16$ is obtained from the initial bound $2Am\log(2Q)$ and loss $1/(8K^3)$, using the global nonnegative floor. This exposes the constant behind (3.34), while the imported interface's hidden exponent remains uniformly quantified rather than numerically invented.
--
--   Differences from the source:
--   - reading: Theorem 3.1 leaves its computation model unnamed → a deterministic unit-cost scalar arithmetic RAM with charged memory access, comparisons, arithmetic and logarithms; reason: the companion Lemma 4.1 names unit-cost arithmetic; no bit-complexity or arbitrary-function oracle is claimed
--   - encoding: a finite directed graph and explicitly maintained approximate distances under edge deletions → integer-indexed vertices and edge identifiers, extended nonnegative distances, scalar flag/value storage and finite instruction runs; reason: this changes no admitted graph, accuracy or legal stream; initialization, each prefix and queries have operational work counts and future updates are absent from the input
--   - encoding: W=m^{O(1)} and total update time m^{1+o(1)}ϵ^{-1} → for every fixed exponent c, constants and one positive subpolynomial overhead are chosen before all inputs with W≤m^c; reason: this pins the asymptotic uniformity rather than allowing constants to depend on a particular graph or accuracy
--   - encoding: T=O(K³Am log(2Q)) in (3.34) → the additional explicit proof-derived bound T≤16K³Am log(2Q) for actual core prefixes; reason: the initial energy bound, exact per-toggle loss and global floor supply 16 directly; no external O-constant is guessed
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #912 (October 2026), p. 6, Theorem 3.1; pp. 7–17, proof, especially equations (3.27), (3.33)–(3.35); pinned PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf

import Mathlib
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Adapters

set_option autoImplicit false
open scoped ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental

/-- Theorem 3.1, with constants uniform for each fixed polynomial-weight exponent.
The source-reachability and incoming-source reductions are not hypotheses on the input. -/
theorem polynomial_weight_sssp :
    ∀ exponent : ℕ, ∃ (p : Program) (C : ℝ) (a : ℕ → ℝ) (queryBound : ℕ),
      0 < C ∧ 0 < queryBound ∧ Subpolynomial a ∧
      (∀ i : Input, i.Valid → 2 ≤ i.n → i.W ≤ i.size ^ exponent →
        1 / (i.size : ℝ) < i.accuracy → i.accuracy < 1 →
        Maintains p C a queryBound false i) ∧
      (∀ (b : Core) (K : ℝ), 32 ≤ K → ∀ choose : State b → CutReply b,
        CutQuality b K choose → ∀ s, Attained b K choose s →
        (s.toggles : ℝ) ≤ 16 * K ^ 3 * A b * b.input.size * Real.log (2 * Q b)) := by sorry

end DecrAlmostLinearSSSP.Decremental
