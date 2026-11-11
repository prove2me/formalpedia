-- Prove2me | Theorems.Thm_DynColorWC_Main_lemma_4_9
-- name    : DynColorWC.Main.lemma_4_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:47:31.329572+00:00
-- url     : https://prove2.me/theorems/d6b2a66a-4f1f-4eaa-b4d6-ae6002d6a2b0
-- title:
--   Lemma 4.9 — ε-connected subsets of V_ε: pairwise |F_ε(u) ∩ F_ε(v)| ≥ (1−4ε)Δ and size ≤ (1+3ε)Δ
-- statement:
--   Let $\varepsilon\in(0,1/10)$, $\Delta\ge10/\varepsilon$, and let $G$ have maximum degree at most $\Delta$. If $S\subseteq V_\varepsilon$ is $\varepsilon$-connected, then
--   1. every pair $u,v\in S$ satisfies $|F_\varepsilon(u)\cap F_\varepsilon(v)|\ge(1-4\varepsilon)\Delta$, and
--   2. $S$ contains at most $(1+3\varepsilon)\Delta$ vertices.
--
--   Differences from the source:
--
--   - encoding: graph of maximum degree at most Δ (standing assumption of §3–§4) → hypothesis ∀ v, G.degree v ≤ Δ on a finite vertex type; reason: the standing assumption made explicit
--   - encoding: S ⊆ V_ε is ε-connected: every pair is joined by a uv-path in G[V_ε] whose edges are ε-friendly (Definition 4.8) → IsEpsConnected: S ⊆ V_ε and every u, v ∈ S are Reachable in the graph of ε-friendly edges of G[V_ε]; reason: a walk contains a path; 'every pair' includes u = v (then the claim is |F_ε(u)| ≥ (1−4ε)Δ)
-- source:
--   Flin and Ghaffari (2026), Dynamic (Δ+1)-Coloring with Polylogarithmic Worst-Case Update Time, STOC 2027 submission, supplied PDF sha256 93ebb2ffd4839b5e525b4550a6569cf5234550ee4a44351aedab3ea3154300e3, Lemma 4.9, p. 19 (PDF 21)

import Mathlib
import Definitions.Def_DynColorWC_Main_AlmostClique

namespace DynColorWC.Main

open Classical in
/-- **Lemma 4.9** (Flin and Ghaffari (2026), STOC 2027 submission, sha256 93ebb2ff…3154300e3,
p. 19 (PDF 21)). Let `ε ∈ (0, 1/10)` and `Δ ≥ 10/ε`, and let `G` have maximum degree at most `Δ`.
If `S ⊆ V_ε` is `ε`-connected then
1. every pair `u, v ∈ S` satisfies `|F_ε(u) ∩ F_ε(v)| ≥ (1 − 4ε)Δ`, and
2. `S` contains at most `(1 + 3ε)Δ` vertices. -/
theorem lemma_4_9 {V : Type} [Fintype V] [DecidableEq V] (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 10)
    (Δ : ℕ) (hΔ : 10 / ε ≤ (Δ : ℝ)) (G : SimpleGraph V) (hdeg : ∀ v, G.degree v ≤ Δ)
    (S : Finset V) (hS : IsEpsConnected ε Δ G S) :
    (∀ u ∈ S, ∀ v ∈ S,
        (1 - 4 * ε) * (Δ : ℝ) ≤ ((friendSet ε Δ G u ∩ friendSet ε Δ G v).card : ℝ)) ∧
      (S.card : ℝ) ≤ (1 + 3 * ε) * Δ := by sorry

end DynColorWC.Main
