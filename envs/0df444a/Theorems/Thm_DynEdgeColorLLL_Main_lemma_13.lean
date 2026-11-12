-- Prove2me | Theorems.Thm_DynEdgeColorLLL_Main_lemma_13
-- name    : DynEdgeColorLLL.Main.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:30.309263+00:00
-- url     : https://prove2.me/theorems/8da2ce1a-edf4-453c-8065-5b6e56585fe3
-- title:
--   Lemma 13 — with a complete $F$, active vertices keep $\deg_{E_a}(w)\le U_d$ in $\bar{\rm A}$
-- statement:
--   Work in the regime of §5.1–§6 ($E\ge D_0$ for an absolute $D_0$, and $\Delta>e^{E}$). Let $G$ have maximum degree at most $\Delta$, fix any directions, any categories in $[m_d]$ and any valid post-shattering choice, and let $F$ be complete (Definition 5). In the modified static algorithm $\bar{\rm A}$ of §6.1 run with $F$, for every node $a$ of depth $d$ and every active vertex $w\in V^\star_a$,
--   $$\deg_{E_a}(w)\le U_d .$$
--
--   With Observation 5 and completeness property (IV), this gives the degree guarantee of $\bar{\rm A}$ at the leaves (Corollary 6).
--
--   Differences from the source:
--   - generalization: post-shattering: per connected component of the bad edges, a deterministic bipartition with discrepancy at most two → any bipartition choice with degree discrepancy at most two at every vertex; reason: the paper's per-component choice is such a choice
--   - reading: "Δ_ε large enough" and Δ > exp(Δ_ε) (PDF p. 23) → an absolute D₀ with the statement for every real E ≥ D₀ and every Δ > exp(E); reason: the existential threshold is the meaning of "large enough"
--   - reading: log in q_d → log base 2; reason: same strength for either base
--   - encoding: random directions and categories → every realization with categories in [m_d]; reason: the statement is deterministic
--   - encoding: F ⊆ V(G) × T → F a set of pairs (vertex, direction list); completeness (I) forces every member to be a node of T; reason: the same sets
-- source:
--   Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), Lemma 13, printed p. 27 (PDF p. 29); Algorithm Ā, printed p. 25 (PDF p. 27); Definitions 3–5, printed p. 24 (PDF p. 26)

import Mathlib
import Definitions.Def_DynEdgeColorLLL_Main_Splitting

namespace DynEdgeColorLLL.Main

open Classical in
/-- Lemma 13 (Peng–Ghaffari, STOC 2027 submission #615, printed p. 27, PDF p. 29). In the regime
of §5.1–§6, for every graph of maximum degree at most `Δ`, every realization of the random choices
and every valid post-shattering choice: if `F` is complete, then for a node `a` of depth `d` and
`w ∈ V⋆_a`, `deg_{E_a}(w) ≤ U_d` in the modified static algorithm Ā of §6.1. -/
theorem lemma_13 :
    ∃ D₀ : ℝ, ∀ E : ℝ, D₀ ≤ E → ∀ Δ : ℕ, Real.exp E < Δ →
      ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (c : Choices V) (post : List Bool → Finset (Sym2 V) → Finset (Sym2 V))
      (F : Set (V × List Bool)),
      (∀ v, G.degree v ≤ Δ) → ValidCategories Δ E G c → IsValidPost post →
      IsComplete Δ E G c F →
      ∀ a : List Bool, a.length ≤ depthR Δ E → ∀ w ∈ (runAbar Δ G c post F a).2,
        (edgeDeg (runAbar Δ G c post F a).1 w : ℝ) ≤ U Δ a.length := by sorry

end DynEdgeColorLLL.Main
