-- Prove2me | Theorems.Thm_DirKECC1549_Main_lemma_5_cost_bound
-- name    : DirKECC1549.Main.lemma_5_cost_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-15T16:14:55.408194+00:00
-- url     : https://prove2.me/theorems/d4b04b35-1000-4475-9540-587f747fbefe
-- title:
--   Lemma 5, analysis: every run of Algorithm 3 costs $O(k^{3k}(m+n)n^{1-\varepsilon_k})$
-- statement:
--   There is an absolute constant $C>0$ such that every cost-annotated run of Algorithm 3 on a directed multigraph $G$ with $n\ge1$ vertices and $m$ edges, with parameter $k\ge1$, has cost
--   $$T\le C\,k^{3k}\,(m+n)\,n^{1-\varepsilon_k},\qquad \varepsilon_k=2^{-(k-1)}.$$
--   The cost is the one of `Alg3CostRun`: every call is charged its local work, and Lemma 1, Lemma 3 and the recursive calls are charged as in the proof of Lemma 5.
--
--   This is the analysis in the proof of Lemma 5 (pp.18–19). For a strongly connected $G$ and $k\ge2$, it combines four facts:
--   - the call with $k-1$ costs $O(k^{3k-3}(m+n)n^{1-\varepsilon_{k-1}})$;
--   - Lemma 1 costs $O(2^k(k+1)!\,n\Delta)$;
--   - there are fewer than $2(k-1)n^{\varepsilon_k}$ hitting-set vertices (Lemma 2), since $\Delta\ge m/n^{\varepsilon_k}$;
--   - each residual call has parameter $k-q\le k-1$, because $q\ge1$ when $G$ is strongly connected.
--
--   Using $\varepsilon_{k-1}=2\varepsilon_k$, so that $n^{\varepsilon_k}\cdot n^{1-\varepsilon_{k-1}}=n^{1-\varepsilon_k}$, the total is at most $\tfrac34 C k^{3k}(m+n)n^{1-\varepsilon_k}$. When $G$ is not strongly connected, the calls on the components $G[S]$ add up to at most $\tfrac34 C k^{3k}(m+n)n^{1-\varepsilon_k}$, because $\sum_S (m_S+n_S)\le m+n$ and $n_S\le n$; the slack absorbs the local work of the call.
--
--   **Formalization note.** The source's $O(k^{3k}mn^{1-\varepsilon_k})$ assumes $m\ge n$ (p.9); the bound here uses $m+n$, which is at most $2m$ on that domain.
-- source:
--   Georgiadis, Kipouridis, Kosinas, Papadopoulos, Pergaminelis, STOC 2027 submission #1549, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1549.pdf, Section 3.3, Lemma 5 and its proof (pp.18-19)

import Mathlib
import Definitions.Def_DirKECC1549_Main_Alg3Cost

set_option autoImplicit false

namespace DirKECC1549.Main

theorem lemma_5_cost_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (G : Fin m → Fin n × Fin n) (k : ℕ)
      (P : Fin n → Fin n → Prop) (T : ℕ), 1 ≤ k → 1 ≤ n → Alg3CostRun n m G k P T →
      (T : ℝ) ≤ C * (k : ℝ) ^ (3 * k) * ((m + n : ℕ) : ℝ) * (n : ℝ) ^ (1 - eps k) := by sorry

end DirKECC1549.Main
