-- Prove2me | Theorems.Thm_AlgebraicFPT_HittingSet_Supplement_extension_retention
-- name    : AlgebraicFPT.HittingSet.Supplement.extension_retention
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:43:40.66012+00:00
-- url     : https://prove2.me/theorems/9c694ad9-5248-4a50-be4b-00f0279bf914
-- title:
--   Theorem 5.2 — Preservation under extension and retention
-- statement:
--   Let $G$ be any finite simple undirected graph, let $k\ge1$ be a natural number, and fix a starting vertex $s$. There exists one simultaneous family $R_{h,s,v}$ of ordered witnesses for all rounds and endpoints, given by the computable initialized maintenance routine. Its first round is $R_{1,s,s}=\{(s)\}$ and $R_{1,s,v}=\varnothing$ for $v\ne s$. For $2\le h\le k$, form
--
--   $$C_{h,s,v}=\bigcup_{w:\,wv\in E(G)}\{P\cdot v:P\in R_{h-1,s,w},\ v\notin V(P)\}.$$
--
--   The new family is exactly $\operatorname{select}(k-h,C_{h,s,v})$, is a subfamily of these legal candidates, and preserves both directions of every candidate-avoidance query of size at most $k-h$.
--
--   Simultaneously, for every $1\le h\le k$ and every endpoint $v$, it consists of genuine simple $h$-vertex paths from $s$ to $v$ and satisfies
--
--   $$R_{h,s,v}\subseteq\mathcal P_{h,s,v},\qquad |R_{h,s,v}|\le\sum_{j=0}^{k-h}h^j.$$
--
--   For every vertex set $Q$ with $|Q|\le k-h$,
--
--   $$\bigl(\exists P\in\mathcal P_{h,s,v}:V(P)\cap Q=\varnothing\bigr)\iff\bigl(\exists P\in R_{h,s,v}:V(P)\cap Q=\varnothing\bigr).$$
--
--   In particular,
--
--   $$\text{a simple }k\text{-vertex path starting at }s\text{ exists}\iff\exists v:\ R_{k,s,v}\ne\varnothing.$$
--
--   This states maintenance under extension and retention, beyond the existence of unrelated representative families at each round. No path existence, connectedness, $k\le n$, or distinct-endpoint promise is required. The subsequent runtime discussion is outside the numbered theorem.
--
--   **Formalization Note** The concrete finite selection routine retains one lexicographically chosen ordered witness per support and branches to depth $k-h$. Its correctness and all bounds are conclusions rather than an input selector contract. The source's bound is used literally, including $B(h,0)=1$.
--
--   Differences from the source:
--   - encoding: finite simple undirected graph with labelled vertices → Mathlib SimpleGraph on Fin n with decidable adjacency; reason: finite relabelling and decidability add no mathematical restriction; n may be zero
--   - encoding: ordered simple h-vertex paths and the sum B(h,k−h) → finite families of length-h vertex lists and an inclusive Finset.range(k−h+1) sum; reason: all orders and all j=0 through k−h terms are retained; h≤k prevents truncation
--   - encoding: families maintained by legal extensions and representative selection → one simultaneous family equal to the initialized computable maintained routine with lexicographic branching selection; reason: a concrete permitted selection is fixed without assuming its properties; the exact bound and candidate and full-family preservation are conclusions
-- source:
--   Liming Cai, Sixiang Zhang, STOC 2027 submission #1035 (October 2026), pp.11–12, Theorem 5.2 (Preservation under extension and retention); proof pp.20–21, Appendix D

import Definitions.Def_AlgebraicFPT_HittingSet_Supplement_Retention

set_option autoImplicit false

namespace AlgebraicFPT.HittingSet.Supplement

/-- Theorem 5.2, pp.11–12; Appendix D, pp.20–21. This is a single initialized,
computable construction for every round and endpoint, including its legal candidates,
representative selection, exact bounds, all queries, and the terminal rooted-path iff. -/
theorem extension_retention {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (hk : 1 ≤ k) (s : Fin n) :
    ∃ R : ℕ → Fin n → Finset (List (Fin n)),
      R = maintained G k s ∧
      (∀ v, R 1 v = if v = s then {[s]} else ∅) ∧
      (∀ h : ℕ, 2 ≤ h → h ≤ k → ∀ v : Fin n,
        let C := extensions G (R (h - 1)) v
        R h v = selectPaths (k - h) C ∧ IsRepresentative (k - h) C (R h v)) ∧
      (∀ h : ℕ, 1 ≤ h → h ≤ k → ∀ v : Fin n,
        R h v ⊆ pathFamily G h s v ∧
        (R h v).card ≤ representativeBound h (k - h) ∧
        ∀ Q : Finset (Fin n), Q.card ≤ k - h →
          (AvoidsQuery (pathFamily G h s v) Q ↔ AvoidsQuery (R h v) Q)) ∧
      ((∃ (v : Fin n) (P : List (Fin n)), IsPath G k s v P) ↔
        ∃ v : Fin n, (R k v).Nonempty) := by sorry

end AlgebraicFPT.HittingSet.Supplement
