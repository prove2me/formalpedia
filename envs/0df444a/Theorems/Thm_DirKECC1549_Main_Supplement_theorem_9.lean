-- Prove2me | Theorems.Thm_DirKECC1549_Main_Supplement_theorem_9
-- name    : DirKECC1549.Main.Supplement.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:21:26.347057+00:00
-- url     : https://prove2.me/theorems/f09a4d63-e99b-42dd-b22f-a079b1dccc03
-- title:
--   Theorem 9 — at most O(n3^{k/3}) k-vertex-connected components of total size O(nk3^{k/3})
-- statement:
--   There is an absolute constant $C>0$ such that for every integer $k\ge1$, every $n$ and every simple undirected graph $G$ with $n$ vertices,
--   $$|C_k(G)|\le C\,n\,3^{k/3}\qquad\text{and}\qquad\|C_k(G)\|=\sum_{K\in C_k(G)}|K|\le C\,n\,k\,3^{k/3},$$
--   where $C_k(G)$ is the family of $k$-vertex-connected components of $G$: the nonempty inclusion-maximal sets of vertices any two of which cannot be separated by fewer than $k$ vertices distinct from them.
--
--   Together with Theorem 10 this determines the exponential growth rate $3^{k/3}$ of the number of $k$-vertex-connected components, up to factors polynomial in $k$; earlier work gave $\|C_k(G)\|=O_k(n)$ without explicit dependence on $k$.
--
--   **Formalization Note** $3^{k/3}$ is the real power. The constant is chosen before $k$, $n$ and $G$; a $k$-dependent constant would make the statement say nothing about the dependence on $k$, which is its content (§6.5.3).
--
--   Differences from the source:
--   - encoding: O(·) in an n-vertex graph, k implicit → one absolute constant C chosen before k ≥ 1, n and G; reason: §6.5 makes the dependence on k explicit and §6.5.3 compares these bounds with Theorem 10 up to factors polynomial in k, so the constant is absolute
--   - encoding: undirected graph G with n vertices → SimpleGraph (Fin n); reason: Lean convention; same instances (k-vertex-connectivity ignores loops and multiplicities)
--   - encoding: k a positive integer (implicit) → hypothesis 1 ≤ k; reason: at k = 0 every pair is 0-vertex-connected, so C_0(G) = {V} has total size n while the bound is 0; the paper's k is a positive integer throughout
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Theorem 9, p.34 (definitions §6.5, p.33)

import Mathlib
import Definitions.Def_DirKECC1549_Main_Supplement_Undirected

set_option autoImplicit false

namespace DirKECC1549.Main.Supplement

/-- Theorem 9, p.34: for an undirected graph `G` with `n` vertices, the number of
`k`-vertex-connected components is `O(n·3^{k/3})` and their total size is `O(n·k·3^{k/3})`. The
constant `C` is absolute: it is chosen before `k`, `n` and `G`. -/
theorem theorem_9 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        ((kvccFamily k G).card : ℝ) ≤ C * (n : ℝ) * (3 : ℝ) ^ ((k : ℝ) / 3) ∧
        (kvccTotalSize k G : ℝ) ≤ C * (n : ℝ) * (k : ℝ) * (3 : ℝ) ^ ((k : ℝ) / 3) := by sorry

end DirKECC1549.Main.Supplement
