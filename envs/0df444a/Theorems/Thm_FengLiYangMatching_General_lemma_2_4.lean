-- Prove2me | Theorems.Thm_FengLiYangMatching_General_lemma_2_4
-- name    : FengLiYangMatching.General.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:48:32.697555+00:00
-- url     : https://prove2.me/theorems/dc5cba9b-d228-436c-9c7b-607b71155a82
-- title:
--   Lemma 2.4 — maximum-matching vertex accounting
-- statement:
--   Throughout, 0≤a<b≤3/8 and 0≤p≤2/3, as imposed on p. 6. Let G be any finite simple undirected unweighted graph, and let M* be any maximum matching of G, used only for analysis. Write OPT=|M*|. H_b consists only of the accepted shadow edges T_b and their times. Put V₁=V(T_a), Y=V\V(T_b). For e∈T_a let Ref(e) be the partners in Y of its endpoints under M*, and k_e=|Ref(e)|. All expectations include the residual arrival times and independent reservation coins.
--
--   For any assignment of arrival times, let U_t count edges of M* with both endpoints unmatched in the shadow matching immediately before t. Let M*₂=M*∩(T_b\T_a); let M*₁Y and M*YY be the optimal edges between V₁ and Y and inside Y. Then
--
--   $$|M^*_{1Y}|+|M^*_{YY}|\ge2\operatorname{OPT}-2|T_b|-U_a+|M^*_2|.$$
--
--   All subtraction is in the real numbers. This accounts for every optimal vertex, including edges accepted in the retain phase.
--
--   Differences from the source:
--   - encoding: arbitrary finite vertex set and unordered simple edges → Fin n for every n including zero, Sym2 edges and finite sets; reason: finite relabelling covers every source instance; loops are excluded in graphs and valid local configurations
--   - generalization: arrival times sampled uniformly from [0,1] → the accounting holds for every real arrival-time assignment, including ties; reason: only the nested shadow matchings T_a⊆T_b and matching property are used; the source random assignment is included
--   - encoding: continuous arrival times with shadow matching at phase boundaries → strict prefixes, half-open reserve/retain phases and fixed sorting of tied times; reason: the phases agree with Algorithm 1; arrivals at any fixed boundary and ties have probability zero; the same convention is used throughout
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, STOC 2027 submission #1018 (October 2026), Lemma 2.4, p. 9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1018.pdf

import Definitions.Def_FengLiYangMatching_General_Local

open MeasureTheory Finset
open scoped BigOperators

namespace FengLiYangMatching.General

theorem lemma_2_4 {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n)
    (hMG : M ⊆ graphEdges G) (hM : IsMatching M) (hmax : M.card = OPT G) (a b p : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 3/8)
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2/3)
    (t : Times G) :
    ((M1Y M a (history G b t)).card : ℝ) + (MYY M (history G b t)).card ≥
      2 * (OPT G : ℝ) - 2 * (shadowAt G t b).card - U G M t a + (M2 G M a b t).card := by sorry

end FengLiYangMatching.General
