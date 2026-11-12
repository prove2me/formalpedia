-- Prove2me | Theorems.Thm_DynEdgeColorLLL_Main_lemma_11
-- name    : DynEdgeColorLLL.Main.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:28.526892+00:00
-- url     : https://prove2.me/theorems/1630b0ad-4d31-4191-b696-63c4d11feb6d
-- title:
--   Lemma 11 — static splitting A: every graph of $\mathcal P_d$ has maximum degree at most $U_d$
-- statement:
--   Work in the regime of §5.1–§6: the threshold $E$ (the paper's $\Delta_\epsilon$) is at least an absolute constant $D_0$, and $\Delta>e^{E}$. Let $G$ be a graph of maximum degree at most $\Delta$. Fix any directions and any categories $\mathrm{cat}_{e,d}\in[m_d]$ for the edges, and any post-shattering choice that splits each bad set with degree discrepancy at most two at every vertex. Run the static splitting algorithm A of §5.2, and let $\mathcal P_d=\{E_a:\mathrm{dep}(a)=d\}$. Then for every $0\le d\le R$, every node $a$ of depth $d$ and every vertex $v$,
--   $$\deg_{E_a}(v)\le U_d .$$
--
--   This is the degree guarantee of the shattering-based splitting [HMN22]. The modified algorithm $\bar{\rm A}$ reuses its discrepancy argument (Lemma 13).
--
--   Differences from the source:
--   - generalization: post-shattering: for every connected component of the bad edges, a deterministic edge bipartition with discrepancy at most two (Euler tour after pairing odd-degree vertices) → any bipartition choice with degree discrepancy at most two at every vertex; reason: every per-component choice of the paper, in particular the Euler-tour one, is such a choice
--   - reading: "We may assume that Δ_ε is large enough" and Δ > exp(Δ_ε) (PDF p. 23) → there is an absolute D₀ such that the statement holds for every real threshold E ≥ D₀ and every Δ > exp(E); reason: the existential threshold is the meaning of "large enough"; Lemma 11 does not involve ε otherwise
--   - reading: log in q_d = 1/log² U_d → log base 2; reason: the paper uses base-2 logarithms for R and B_e (PDF p. 37); both bases give statements of the same strength
--   - encoding: random directions and categories → the statement holds for every realization with categories in [m_d] for every edge of G and depth d < R; reason: Lemma 11 is deterministic; categories outside [m_d] never occur
--   - encoding: nodes of the full binary tree T of depth R → direction lists of length at most R; the root is the empty list; reason: a node is identified with its root path
-- source:
--   Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), Lemma 11, printed p. 23 (PDF p. 25); Algorithm A, printed p. 22 (PDF p. 24); parameters and "Δ_ε large enough", printed p. 21 (PDF p. 23)

import Mathlib
import Definitions.Def_DynEdgeColorLLL_Main_Splitting

namespace DynEdgeColorLLL.Main

open Classical in
/-- Lemma 11 (Peng–Ghaffari, STOC 2027 submission #615, printed p. 23, PDF p. 25). In the regime of
§5.1–§6 (`Δ_ε` large enough, `Δ > exp(Δ_ε)`), for every graph of maximum degree at most `Δ`, every
realization of the directions and categories and every valid post-shattering choice, the static
splitting algorithm A of §5.2 satisfies: for every `0 ≤ d ≤ R`, the maximum degree of any graph in
`P_d = {E_a : dep(a) = d}` is at most `U_d`. -/
theorem lemma_11 :
    ∃ D₀ : ℝ, ∀ E : ℝ, D₀ ≤ E → ∀ Δ : ℕ, Real.exp E < Δ →
      ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (c : Choices V) (post : List Bool → Finset (Sym2 V) → Finset (Sym2 V)),
      (∀ v, G.degree v ≤ Δ) → ValidCategories Δ E G c → IsValidPost post →
      ∀ d ≤ depthR Δ E, ∀ a : List Bool, a.length = d → ∀ v : V,
        (edgeDeg (runA Δ G c post a) v : ℝ) ≤ U Δ d := by sorry

end DynEdgeColorLLL.Main
