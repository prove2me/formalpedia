-- Prove2me | Theorems.Thm_AlmostKing_Query_theorem_1
-- name    : AlmostKing.Query.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:46.534754+00:00
-- url     : https://prove2.me/theorems/bd8a4f47-f2b4-4ee9-95fb-3a9e3cee0f5c
-- title:
--   Theorem 1 — an almost king with $O_ε(n^{4/3})$ queries
-- statement:
--   For every fixed real $\varepsilon$ with $0<\varepsilon<1$, there exists a constant $C>0$, depending only on $\varepsilon$, such that for every integer $n\ge1$ there is a deterministic query decision tree $t$ on $n$ vertices. For every tournament $T$ on those vertices,
--   $$\mathrm{queries}_t(T)\le Cn^{4/3},\qquad |N_T^{++}(t(T))|\ge(1-\varepsilon)(n-1).$$
--   The query count is the number of queries on the path followed by the actual oracle answers, and the bound holds for every input tournament. The output is a $(1-\varepsilon)$-king of the whole tournament. No template, courts, or regular partition is assumed in this statement.
--
--   This is the paper's main theorem: deterministic search controls every fixed fraction below one within a query bound of order $n^{4/3}$.
--
--   Differences from the source:
--   - encoding: $[n]=\{1,\ldots,n\}$ → $\mathrm{Fin}\,n=\{0,\ldots,n-1\}$; reason: relabeling by an order-preserving bijection preserves all graph and counting conditions
--   - encoding: positive integer $n$ as in §2 → the explicit hypothesis $1\le n$; reason: there is no vertex to output on an empty tournament
--   - reading: an asymptotic $O_\varepsilon(n^{4/3})$ bound → one positive constant $C$ valid for every $n\ge1$, before the quantifier over $n$; reason: p. 8 handles the finitely many small sizes by querying the whole tournament
--   - reading: a deterministic query algorithm with known input size → one finite adaptive query tree per input size; reason: the query model counts only oracle calls and p. 12 explicitly treats computation as free
--   - encoding: an oracle query reveals the direction between two vertices → self-queries are also permitted, always return false, and cost one; reason: a self-query has a predetermined answer on every tournament and can be removed without changing the output or increasing cost
-- source:
--   Ziad Ismaili Alaoui, Oded Lachish, Nikhil S. Mande, A King for Almost Everyone, STOC 2027 submission #472 (October 2026), SHA-256 c262b203b2088dcae48025a77e016df4cc78f93c1856a6fac580c7577d8dea92, Theorem 1 (Main); algorithm and proof p. 8, p. 2. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/472.pdf

import Mathlib
import Definitions.Def_AlmostKing_Query_Goal

namespace AlmostKing.Query

/-- Theorem 1 (Main), p. 2. The positive constant depends only on ε.
The bound is on every tournament's evaluation path, and the output is a king of that whole tournament. -/
theorem theorem_1 : ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∃ t : QueryTree n,
      ∀ T : Digraph (Fin n), IsTournament T →
        (t.queries T : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3) ∧
          IsDeltaKing T (1 - ε) (t.eval T) := by sorry

end AlmostKing.Query
