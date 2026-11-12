-- Prove2me | Theorems.Thm_DynEdgeColorLLL_Main_corollary_6
-- name    : DynEdgeColorLLL.Main.corollary_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:30.558434+00:00
-- url     : https://prove2.me/theorems/ebb71a26-6cc9-4704-8b9b-436ca2178d9e
-- title:
--   Corollary 6 — with a complete $F$, every leaf graph of $\bar{\rm A}$ has maximum degree at most $U_R$
-- statement:
--   Work in the regime of §5.1–§6. Let $G$ have maximum degree at most $\Delta$, fix any directions, any categories in $[m_d]$ and any valid post-shattering choice, and let $F$ be complete. Then in the modified static algorithm $\bar{\rm A}$ run with $F$, every graph in $\mathcal P_R=\{E_a:a\in L_T\}$ has maximum degree at most $U_R$:
--   $$\deg_{E_a}(w)\le U_R\quad\text{for every leaf }a\text{ and every vertex }w .$$
--
--   Theorem 4 feeds these leaf graphs to Lemma 9; this corollary is the degree bound that makes that possible.
--
--   Differences from the source:
--   - generalization: post-shattering: per connected component of the bad edges, a deterministic bipartition with discrepancy at most two → any bipartition choice with degree discrepancy at most two at every vertex; reason: the paper's per-component choice is such a choice
--   - reading: "Δ_ε large enough" and Δ > exp(Δ_ε) (PDF p. 23) → an absolute D₀ with the statement for every real E ≥ D₀ and every Δ > exp(E); reason: the existential threshold is the meaning of "large enough"
--   - reading: log in q_d → log base 2; reason: same strength for either base
--   - encoding: random directions and categories → every realization with categories in [m_d]; reason: the statement is deterministic
--   - encoding: F ⊆ V(G) × T → F a set of pairs (vertex, direction list); completeness (I) forces every member to be a node of T; reason: the same sets
-- source:
--   Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), Corollary 6, printed p. 28 (PDF p. 30)

import Mathlib
import Definitions.Def_DynEdgeColorLLL_Main_Splitting

namespace DynEdgeColorLLL.Main

open Classical in
/-- Corollary 6 (Peng–Ghaffari, STOC 2027 submission #615, printed p. 28, PDF p. 30). In the regime
of §5.1–§6, for every graph of maximum degree at most `Δ`, every realization of the random choices
and every valid post-shattering choice: if `F` is complete, then every graph in
`P_R = {E_a : a ∈ L_T}` produced by Ā has maximum degree at most `U_R`. -/
theorem corollary_6 :
    ∃ D₀ : ℝ, ∀ E : ℝ, D₀ ≤ E → ∀ Δ : ℕ, Real.exp E < Δ →
      ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (c : Choices V) (post : List Bool → Finset (Sym2 V) → Finset (Sym2 V))
      (F : Set (V × List Bool)),
      (∀ v, G.degree v ≤ Δ) → ValidCategories Δ E G c → IsValidPost post →
      IsComplete Δ E G c F →
      ∀ a : List Bool, a.length = depthR Δ E → ∀ w : V,
        (edgeDeg (runAbar Δ G c post F a).1 w : ℝ) ≤ U Δ (depthR Δ E) := by sorry

end DynEdgeColorLLL.Main
