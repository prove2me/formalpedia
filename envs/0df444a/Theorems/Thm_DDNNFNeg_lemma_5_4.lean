-- Prove2me | Theorems.Thm_DDNNFNeg_lemma_5_4
-- name    : DDNNFNeg.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:22:45.650201+00:00
-- url     : https://prove2.me/theorems/0e0c7092-86f5-4507-850d-08ddfb6b7ce1
-- title:
--   Lemma 5.4 — $\Omega(n)$ crossing edges of one colour with pairwise disjoint neighbourhoods
-- statement:
--   Let $\gamma \in (0,1)$. There are $\kappa > 0$ and $n_0$, depending only on $\gamma$, such that for every $n \ge n_0$, every simple 3-regular balanced-cut $\gamma$-edge expander $G$ on $[n]$ with a proper 3-edge-colouring $c$, and every balanced partition $(A, B)$ of $[n]$, there are a colour and a set $M$ of edges of $G$ with:
--
--   1. every $e \in M$ is a crossing edge of $(A, B)$ of that colour;
--   2. the neighbourhoods $N(e)$, $e \in M$, are pairwise disjoint;
--   3. $|M| \ge \kappa n$.
--
--   In the paper's words: the graph has $\Omega(n)$ crossing edges of the same colour whose neighbourhoods are pairwise disjoint. These edges are the coordinates on which the rectangle bound of Lemmas 5.5–5.6 is proved.
--
--   Differences from the source:
--   - generalization: G as promised by Proposition 5.2, with its fixed γ → every γ ∈ (0,1), with constants depending only on γ; reason: the paper's γ is one instance
--   - reading: Ω(n) → ≥ κn for all n ≥ n₀, with κ > 0 and n₀ depending only on γ; reason: the standard reading of Ω
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Lemma 5.4, p.13

import Mathlib
import Definitions.Def_DDNNFNeg_IsBalancedCutExpander
import Definitions.Def_DDNNFNeg_IsProperEdgeColoring
import Definitions.Def_DDNNFNeg_edgeNbhd

namespace DDNNFNeg

/-- **Lemma 5.4** (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), p.13): for any balanced partition `(A, B)` of `V`, the graph `G` has
`Ω(n)` crossing edges of the same colour whose neighbourhoods are pairwise disjoint.

**Formalization Note** The setting is that of §5.2: `G` a simple 3-regular balanced-cut
`γ`-edge expander on `Fin n` with a proper 3-edge-colouring `c`. The paper fixes one `γ`
(Proposition 5.2); here `γ ∈ (0, 1)` is arbitrary and `Ω(n)` is read as `≥ κ n` for all
`n ≥ n₀`, with `κ > 0` and `n₀` depending only on `γ`. The edges form a set `M` of edges of
`G` (so they are distinct). -/
theorem lemma_5_4 (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.IsRegularOfDegree 3 →
      IsBalancedCutExpander γ G → ∀ c : Sym2 (Fin n) → Fin 3, IsProperEdgeColoring G c →
      ∀ A : Finset (Fin n), IsBalanced A →
      ∃ (col : Fin 3) (M : Finset (Sym2 (Fin n))), M ⊆ G.edgeFinset ∧
        (∀ e ∈ M, IsCrossing A e ∧ c e = col) ∧
        (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' → Disjoint (edgeNbhd G e) (edgeNbhd G e')) ∧
        κ * n ≤ (M.card : ℝ) := by sorry

end DDNNFNeg
