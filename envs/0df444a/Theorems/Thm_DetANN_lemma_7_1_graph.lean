-- Prove2me | Theorems.Thm_DetANN_lemma_7_1_graph
-- name    : DetANN.lemma_7_1_graph
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:27:35.260651+00:00
-- url     : https://prove2.me/theorems/1aac5ad8-a07f-4d2f-8c68-4a52b1a65557
-- title:
--   Proof of Lemma 7.1, p.20 — an explicit 16-regular undirected multigraph on $[2^k]$ with mean-zero contraction $\theta_0=5\sqrt2/8<1$
-- statement:
--   Let $\theta_0=5\sqrt2/8$. For every power of two $d=2^k$, the graph of the proof of Lemma 7.1 on $[d]$ — the Margulis–Gabber–Galil graph on $\mathbb Z_m^2$ with every occurrence duplicated if $d=m^2$, its product with $\{0,1\}$ if $d=2m^2$, and the single vertex with 16 loops if $d=1$ — is a $16$-regular undirected multigraph whose normalized adjacency matrix $W$ satisfies
--
--   $$\|Wf\|_2\le\theta_0\|f\|_2\qquad\text{for every }f\in\mathbb R^d\text{ with }\sum_vf(v)=0,$$
--
--   and $0<\theta_0<1$.
--
--   This is the graph content of Lemma 7.1 with the explicit constants $\Delta=16$, $\theta_0=5\sqrt2/8$ of its proof.
--
--   **Formalization Note** The graph is the definition `DetANN.lemma71Nbr`; the operation count of Lemma 7.1 is part of the resource bounds of Theorem 1.1, not of this statement.
--
--   Differences from the source:
--   - encoding: a graph on ℤ²_m or ℤ²_m × {0, 1} regarded as a graph on [d] → the same graph transported to Fin (2^k) by a fixed bijection; degree 16 as neighbor lists indexed by Fin 16; reason: Lemma 7.1 asks for a graph on [d]; relabeling vertices changes nothing
--   - encoding: ‖Wf‖₂ ≤ θ₀‖f‖₂ → Σ_u (Wf)_u² ≤ θ₀² Σ_v f_v²; reason: equivalent for θ₀ ≥ 0
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), Proof of Lemma 7.1, Appendix B, p.20 (PDF p.20); Lemma 7.1, p.17

import Mathlib
import Definitions.Def_DetANN_Multigraph
import Definitions.Def_DetANN_MGG

namespace DetANN

/-- **Proof of Lemma 7.1, the graphs** (Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), Appendix B, p.20; Lemma 7.1, p.17).
For every power of two `d = 2^k`, the explicit graph of the proof of Lemma 7.1 on `[d]` (built from the
Margulis–Gabber–Galil graph) is a `16`-regular undirected multigraph whose normalized adjacency matrix
`W` satisfies `‖W f‖ ≤ θ₀‖f‖` for every mean-zero `f`, with `θ₀ = 5√2/8 < 1`.

**Formalization Note.** This is the graph content of Lemma 7.1 with the explicit constants `Δ = 16`
and `θ₀ = 5√2/8` of its proof; the clause "the neighbor lists can be constructed in `O(d)` arithmetic
operations" is not stated here (the resource bounds of `DetANN.theorem_1_1` account for it).
Regularity is the type `Fin 16` of the neighbor lists. The spectral bound is stated squared. -/
theorem lemma_7_1_graph (k : ℕ) :
    0 < theta0 ∧ theta0 < 1 ∧ IsUndirected (lemma71Nbr k) ∧
      ContractsMeanZero (adjMatrix (lemma71Nbr k)) theta0 := by sorry

end DetANN
