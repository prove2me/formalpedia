-- Prove2me | Theorems.Thm_EulerSparsify_Supplement_theorem_4_1
-- name    : EulerSparsify.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:33:34.48128+00:00
-- url     : https://prove2.me/theorems/8c7879e8-166b-4051-bd8a-08fa31e88ee2
-- title:
--   Theorem 4.1 — a $(\rho,\gamma)$-strong ER clustering with $\rho=O\bigl(\tfrac{n}{w(E)}\gamma\log^2\gamma\bigr)$ for every $\gamma\ge100$
-- statement:
--   There is an algorithm which, given any weighted graph $G=(V,E,w)$ with $n=|V|$ and any $\gamma\ge100$, computes a $(\rho,\gamma)$-strong effective resistance clustering $\{U_i\}_{i\in[I]}$ of $G$ (Definition 3.6), where
--   $$\rho=O\Bigl(\frac{n}{w(E)}\,\gamma\log^2\gamma\Bigr).$$
--
--   Precisely: there is a universal constant $C>0$ such that
--
--   1. **existence:** for every finite graph with weights $w_e\ge0$ and total weight $w(E)>0$, and every real $\gamma\ge100$, there is a partition $\{U_i\}$ of $V$ such that every induced subgraph $G[U_i]$ is connected with $\mathrm{diam}_{\mathrm{ER}}(G[U_i])\le C\,n\,\gamma\log^2\gamma/w(E)$, and the edges not inside any $G[U_i]$ have total weight at most $w(E)/\gamma$;
--   2. **algorithm:** one Turing machine, given a finite graph with nonnegative rational weights and positive total weight and a rational $\gamma\ge100$ in binary, outputs such a partition of that graph, with the same constant $C$.
--
--   Here $\log$ is the natural logarithm. The graph need not be connected.
--
--   The diameter bound depends nearly linearly on the fraction $1/\gamma$ of weight cut. The paper states it as the first of the two single-scale decomposition results of Section 4, and proves it with the electrical level-set argument of Section 7 (Theorem 7.1, Corollary 7.2, Algorithm 7.1).
--
--   **Formalization Note** The machine is a Mathlib `Turing.TM2Computable` function from the instance encoding `encClusterIn` to the base mission's `encVertexLists`; output parts are read with `partsOfLists`. No running time is claimed, as in the source.
--
--   Differences from the source:
--   - encoding: ρ = O((n/w(E)) γ log² γ) → ρ = C · n · γ · log² γ / w(E) with one C > 0 chosen before the graph and γ; reason: the meaning of O(·); the proof gives C = 10⁵ (p.40)
--   - encoding: "given any G = (V, E, w)" → also w(E) > 0; reason: n/w(E) is undefined at w(E) = 0, so this only excludes the undefined case
--   - reading: diam_ER(G[U_i]) ≤ ρ → also G[U_i] connected through positive-weight edges; reason: ER across components is +∞; the pseudoinverse formula would trivialize the bound
--   - reading: "There is an algorithm which … computes" → one Turing machine (Mathlib TM2Computable) on binary rational inputs with no time bound, plus existence for every real-weighted graph and real γ ≥ 100; reason: a Turing machine reads finite inputs; the theorem states no running time
--   - generalization: graph G = (V, E, w) → parallel edges and self-loops allowed; reason: parallel edges can be merged without changing any quantity; a loop is never cut and the loop-free case gives the looped one with a larger constant (apply it with γ' = γ·w(non-loop edges)/w(E) when this is ≥ 100, singletons when it is ≤ 1, and γ' = 100 otherwise), so the statement specializes to the source's graphs
--   - encoding: partition {U_i}_{i∈[I]} → family indexed by Fin I, disjoint and covering, empty parts allowed; reason: an empty part has no edges and satisfies the diameter bound vacuously
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Theorem 4.1, p.12 (PDF p.14); proof in §7.3, pp.37–40 (PDF pp.39–42)

import Mathlib
import Definitions.Def_EulerSparsify_Supplement_IsStrongERClustering
import Definitions.Def_EulerSparsify_Supplement_encClusterIn
import Definitions.Def_EulerSparsify_encVertexLists

namespace EulerSparsify

namespace Supplement

/-- **Theorem 4.1** (strong ER clustering with `ρ = O(n γ log² γ / w(E))`), p.12, PDF p.14;
proved in §7.3, pp.37–40 (PDF pp.39–42).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Theorem 4.1: "There is an
algorithm which given any G = (V, E, w) with n = |V| and γ ≥ 100, computes a (ρ, γ)-strong ER
clustering, where ρ = O((n / w(E)) γ log² γ)."

There is a universal constant `C > 0` such that
* (existence) every finite weighted graph `G` with weights `w ≥ 0` and total weight `w(E) > 0`,
  and every real `γ ≥ 100`, has a `(C · n · γ · log² γ / w(E), γ)`-strong ER clustering
  (Definition 3.6, `IsStrongERClustering`), with `n = |V|`; and
* (algorithm) one Turing machine `alg`, on every well-formed rational weighted input graph with
  positive total weight and every rational `γ ≥ 100`, outputs such a clustering of that graph, with
  the same `C`.

**Formalization Note.**
* `O(·)` is one universal constant `C`, chosen before the graph and `γ` (the proof gives
  `R ≤ 10⁵ · (n/w(E)) γ log² γ`, p.40).
* `log` is the natural logarithm (`Real.log`; p.7: "All logarithms are base e unless otherwise
  specified").
* `w(E) > 0` is assumed so that `n/w(E)` is defined.
* The graph need not be connected (the paper runs the algorithm on each component, p.34).
  Parallel edges and self-loops are allowed.
* "There is an algorithm which … computes" carries no time bound; the machine is a Mathlib
  `Turing.TM2Computable` function with binary input `encClusterIn` and output `encVertexLists`,
  and its output parts are read with `partsOfLists`. -/
theorem theorem_4_1 :
    ∃ C : ℝ, 0 < C ∧
      (∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
          (G : DiGraph V E), (∀ e, 0 ≤ G.w e) → 0 < ∑ e, G.w e → ∀ γ : ℝ, 100 ≤ γ →
          ∃ (I : ℕ) (U : Fin I → Finset V),
            IsStrongERClustering G
              (C * (Fintype.card V : ℝ) * γ * Real.log γ ^ 2 / ∑ e, G.w e) γ U) ∧
      ∃ alg : RatDigraph × ℚ → List (List ℕ),
        Nonempty (Turing.TM2Computable encClusterIn encVertexLists alg) ∧
        ∀ (Gr : RatDigraph) (hG : Gr.WellFormed) (γ : ℚ), (100 : ℝ) ≤ (γ : ℝ) →
          0 < ∑ e, (Gr.toDiGraph hG).w e →
          IsStrongERClustering (Gr.toDiGraph hG)
            (C * (Gr.1 : ℝ) * (γ : ℝ) * Real.log (γ : ℝ) ^ 2 / ∑ e, (Gr.toDiGraph hG).w e)
            (γ : ℝ) (partsOfLists Gr.1 (alg (Gr, γ))) := by sorry

end Supplement

end EulerSparsify
