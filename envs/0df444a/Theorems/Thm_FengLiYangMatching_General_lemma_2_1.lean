-- Prove2me | Theorems.Thm_FengLiYangMatching_General_lemma_2_1
-- name    : FengLiYangMatching.General.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:48:17.907611+00:00
-- url     : https://prove2.me/theorems/b055aa30-ea33-4b8c-b470-ee2435b4ca98
-- title:
--   Lemma 2.1 — local reservation-averaged recovery
-- statement:
--   Throughout, 0≤a<b≤3/8 and 0≤p≤2/3, as imposed on p. 6. Let G be any finite simple undirected unweighted graph, and let M* be any maximum matching of G, used only for analysis. Write OPT=|M*|. H_b consists only of the accepted shadow edges T_b and their times. Put V₁=V(T_a), Y=V\V(T_b). For e∈T_a let Ref(e) be the partners in Y of its endpoints under M*, and k_e=|Ref(e)|. All expectations include the residual arrival times and independent reservation coins.
--
--   For an early shadow edge e, let N̂_e count its endpoints matched during recovery only, and R̂_e count its reference vertices matched during recovery, regardless of their partner or e's reservation decision. If e was accepted earlier, N̂_e=0. Conditional on H_b, for every e∈T_a,
--
--   $$\frac32\mathbb E[\widehat N_e\mid H_b]+\mathbb E[\widehat R_e\mid H_b]\ge\frac{3p}2 k_e.$$
--
--   This local inequality averages the actual reservation choice and credits reference vertices even when e is not reserved.
--
--   Differences from the source:
--   - encoding: arbitrary finite vertex set and unordered simple edges → Fin n for every n including zero, Sym2 edges and finite sets; reason: finite relabelling covers every source instance; loops are excluded in graphs and valid local configurations
--   - encoding: conditional on the exact accepted-edge history H_b → almost every history under its pushforward law, integrated against the explicit residual product law; reason: exact histories can have zero probability; Lemma 4.1 asserts measurability and disintegration, identifying this law as the conditional distribution
--   - encoding: expectations of finite vertex or edge counts → integrability is asserted in the conclusion together with the bound; reason: bounded measurable counts are integrable under the probability laws; this is an obligation, not an additional hypothesis
--   - encoding: continuous arrival times with shadow matching at phase boundaries → strict prefixes, half-open reserve/retain phases and fixed sorting of tied times; reason: the phases agree with Algorithm 1; arrivals at any fixed boundary and ties have probability zero; the same convention is used throughout
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, STOC 2027 submission #1018 (October 2026), Lemma 2.1, p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1018.pdf

import Definitions.Def_FengLiYangMatching_General_Local

open MeasureTheory Finset
open scoped BigOperators

namespace FengLiYangMatching.General

theorem lemma_2_1 {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n)
    (hMG : M ⊆ graphEdges G) (hM : IsMatching M) (hmax : M.card = OPT G) (a b p : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 3/8)
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2/3) :
    ∀ᵐ h ∂historyLaw G b, ∀ e ∈ early a h,
      Integrable (Nhat G a b e) (conditionalLaw G b p h) ∧
      Integrable (Rhat G M a b h e) (conditionalLaw G b p h) ∧
      (3/2 : ℝ) * (∫ w, Nhat G a b e w ∂conditionalLaw G b p h) +
        (∫ w, Rhat G M a b h e w ∂conditionalLaw G b p h)
        ≥ (3*p/2) * (references M h e).card := by sorry

end FengLiYangMatching.General
