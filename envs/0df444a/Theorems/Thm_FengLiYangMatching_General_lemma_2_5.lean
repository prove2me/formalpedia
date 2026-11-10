-- Prove2me | Theorems.Thm_FengLiYangMatching_General_lemma_2_5
-- name    : FengLiYangMatching.General.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:48:18.455208+00:00
-- url     : https://prove2.me/theorems/da1af8f0-5ffb-47ae-8cc3-40fd28156060
-- title:
--   Lemma 2.5 — retain-phase vertex accounting
-- statement:
--   Throughout, 0≤a<b≤3/8 and 0≤p≤2/3, as imposed on p. 6. Let G be any finite simple undirected unweighted graph, and let M* be any maximum matching of G, used only for analysis. Write OPT=|M*|. H_b consists only of the accepted shadow edges T_b and their times. Put V₁=V(T_a), Y=V\V(T_b). For e∈T_a let Ref(e) be the partners in Y of its endpoints under M*, and k_e=|Ref(e)|. All expectations include the residual arrival times and independent reservation coins.
--
--   For any arrival-time assignment, U_t counts optimal edges with both endpoints unmatched in T_t, and M*₂=M*∩(T_b\T_a). Then
--
--   $$2(|T_b|-|T_a|)\ge U_a-U_b+|M^*_2|.$$
--
--   The differences are signed real differences, not truncated cardinality subtraction. This relates retain-phase matched vertices to optimal edges that cease to be completely unmatched.
--
--   Differences from the source:
--   - encoding: arbitrary finite vertex set and unordered simple edges → Fin n for every n including zero, Sym2 edges and finite sets; reason: finite relabelling covers every source instance; loops are excluded in graphs and valid local configurations
--   - generalization: arrival times sampled uniformly from [0,1] → the accounting holds for every real arrival-time assignment, including ties; reason: the proof uses only nested shadow matchings; this includes every source realization
--   - encoding: continuous arrival times with shadow matching at phase boundaries → strict prefixes, half-open reserve/retain phases and fixed sorting of tied times; reason: the phases agree with Algorithm 1; arrivals at any fixed boundary and ties have probability zero; the same convention is used throughout
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, STOC 2027 submission #1018 (October 2026), Lemma 2.5, p. 9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1018.pdf

import Definitions.Def_FengLiYangMatching_General_Local

open MeasureTheory Finset
open scoped BigOperators

namespace FengLiYangMatching.General

theorem lemma_2_5 {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n)
    (hMG : M ⊆ graphEdges G) (hM : IsMatching M) (hmax : M.card = OPT G) (a b p : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 3/8)
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2/3)
    (t : Times G) :
    2 * ((shadowAt G t b).card - (shadowAt G t a).card : ℝ) ≥
      U G M t a - U G M t b + (M2 G M a b t).card := by sorry

end FengLiYangMatching.General
