-- Prove2me | Theorems.Thm_EulerSparsify_lemma_4_2
-- name    : EulerSparsify.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:38:39.895663+00:00
-- url     : https://prove2.me/theorems/cb8e4c27-6373-4f00-b64d-d4c6ad368feb
-- title:
--   Lemma 4.2 — one-level partition with ER diameter $O_{p,\eta}(1/\beta)$ and potential-charged cut size, in polynomial time
-- statement:
--   There is a deterministic polynomial-time algorithm with the following guarantee. For all $p\in(\tfrac12,1)$ and $\eta\in(0,1)$ there is a constant $C=C(p,\eta)>0$ such that, given any unweighted graph $G=(V,E)$ and $\beta>0$, it computes a partition $\{U_i\}_{i\in[I]}$ of $V$ with
--
--   1. **ER diameter:** every $G[U_i]$ is connected and $\mathrm{diam}_{\mathrm{ER}}(G[U_i])\le C/\beta$;
--   2. **cut size:**
--   $$\Bigl|E\setminus\bigcup_{i\in[I]}E(G[U_i])\Bigr|\le\eta\beta^{1-p}\Bigl[\sum_{i\in[I]}\bigl(\beta|U_i|+\mathrm{vol}_G(U_i)\bigr)^p-\bigl(\beta|V|+\mathrm{vol}(G)\bigr)^p\Bigr].$$
--
--   Formally there are two clauses with the same $C$: every finite unweighted graph and every real $\beta>0$ admit such a partition, and one Turing machine outputs such a partition on every rational instance $(G,\beta,p,\eta)$ in time polynomial in the binary input length.
--
--   The cut is charged to the increase of a concave potential of the regularized volumes, which lets Algorithm 4.1 charge the cuts of all weight scales to one potential (Proposition 4.3).
--
--   **Formalization Note** The machine reads $(G,\beta,p,\eta)$ (`encLevelIn`) and writes a list of vertex lists (`encVertexLists`).
--
--   Differences from the source:
--   - encoding: diam_ER(G[U_i]) ≤ O_{p,η}(1/β) → ≤ C/β, C chosen after p, η and before the graph and β; reason: the meaning of O_{p,η}
--   - reading: diam_ER(G[U_i]) ≤ … → also G[U_i] connected; reason: ER across components is +∞; the pseudoinverse formula would trivialize the bound
--   - reading: "There is a polynomial time algorithm" → one deterministic TM2 machine on binary rational β, p, η, plus existence for every real β > 0; reason: a Turing machine reads finite inputs; the algorithm uses no randomness
--   - generalization: unweighted graph → parallel edges and self-loops allowed; reason: Algorithm 4.1 applies the lemma to multigraphs; a loop is never cut and only enlarges the right side of item 2
--   - encoding: partition {U_i}_{i∈[I]} → family indexed by Fin I, disjoint and covering, empty parts allowed; reason: an empty part contributes 0^p = 0
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Lemma 4.2, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_EulerSparsify_IsLevelPartition
import Definitions.Def_EulerSparsify_RatGraphU
import Definitions.Def_EulerSparsify_encLevelIn
import Definitions.Def_EulerSparsify_encVertexLists

namespace EulerSparsify

/-- **Lemma 4.2** (one-level partition with potential-charged cut size), p.12, PDF p.14.
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Lemma 4.2: "There is a polynomial time algorithm that given any unweighted graph G = (V, E),
with n = |V| and m = |E|, and parameters β > 0, p ∈ (1/2, 1) and η ∈ (0, 1) computes a
partitioning {U_i}_{i∈[I]} of the vertices such that
1. ER diameter: diam_ER(G[U_i]) ≤ O_{p,η}(1/β)
2. Cut size: |E ∖ ⋃_{i∈[I]} E(G[U_i])| ≤ ηβ^{1−p} [Σ_{i∈I} (β|U_i| + vol_G(U_i))^p − (β|V| + vol(G))^p]"

There is one Turing machine `alg`, polynomial time in the binary input length, such that for all
`p ∈ (1/2, 1)`, `η ∈ (0, 1)` there is `C = C(p, η) > 0` with
* (existence) every finite unweighted graph and every real `β > 0` admit a partition satisfying
  items 1–2 with diameter bound `C/β` (`IsLevelPartition`), and
* (algorithm) on every unweighted input graph and rational `β > 0`, `p`, `η`, the machine outputs
  such a partition, with the same `C`.

**Formalization Note.** `O_{p,η}(1/β)` is `C(p,η)/β` with `C` chosen after `p`, `η` and before the
graph and `β`. Unweighted = all weights `1`; parallel edges and self-loops are allowed (a loop is
never cut and only enlarges the right side of item 2). The diameter bound includes connectivity of
`G[U_i]` (`DiGraph.DiamERLe`). Inputs and outputs are binary (`encLevelIn`, `encVertexLists`);
the output parts are read with `partsOfLists`. -/
theorem lemma_4_2 :
    ∃ alg : RatGraphU × ℚ × ℚ × ℚ → List (List ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime encLevelIn encVertexLists alg) ∧
      ∀ p η : ℝ, 1 / 2 < p → p < 1 → 0 < η → η < 1 →
        ∃ C : ℝ, 0 < C ∧
          (∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
              (G : DiGraph V E), (∀ e, G.w e = 1) → ∀ β : ℝ, 0 < β →
              ∃ (I : ℕ) (U : Fin I → Finset V), IsLevelPartition G β p η C U) ∧
          (∀ (Gr : RatGraphU) (hG : Gr.WellFormed) (β p' η' : ℚ), 0 < β →
              (p' : ℝ) = p → (η' : ℝ) = η →
              IsLevelPartition (Gr.toDiGraph hG) (β : ℝ) p η C
                (partsOfLists Gr.1 (alg (Gr, β, p', η')))) := by sorry

end EulerSparsify
