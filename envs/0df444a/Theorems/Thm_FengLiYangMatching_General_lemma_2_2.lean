-- Prove2me | Theorems.Thm_FengLiYangMatching_General_lemma_2_2
-- name    : FengLiYangMatching.General.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:48:10.382198+00:00
-- url     : https://prove2.me/theorems/d040e82e-9d1b-48de-a2d0-82d186b9ad0e
-- title:
--   Lemma 2.2 — coupled Greedy recovery comparison
-- statement:
--   Throughout, 0≤a<b≤3/8 and 0≤p≤2/3, as imposed on p. 6. Let G be any finite simple undirected unweighted graph, and let M* be any maximum matching of G, used only for analysis. Write OPT=|M*|. H_b consists only of the accepted shadow edges T_b and their times. Put V₁=V(T_a), Y=V\V(T_b). For e∈T_a let Ref(e) be the partners in Y of its endpoints under M*, and k_e=|Ref(e)|. All expectations include the residual arrival times and independent reservation coins.
--
--   Fix e∈T_a. Conditional on H_b, form B from all YY recovery edges and post-b edges from other reserved vertices to Y, excluding both endpoints of e. This construction is independent of the reservation coin of e. Add those endpoints and their post-b edges to Y to obtain B_e. Greedy on B and B_e uses identical arrival times on their common edges. Let N count matched endpoints of e in B_e, R matched vertices of Ref(e) in B_e, and K matched vertices of Ref(e) in B. For almost every H_b and every background B with positive conditional probability,
--
--   $$\mathbb E[3N+2R+K\mid H_b,B]\ge3k_e.$$
--
--   This includes k_e=0,1,2 and supplies the conditional recovery comparison before averaging the distinguished reservation coin.
--
--   Differences from the source:
--   - encoding: arbitrary finite vertex set and unordered simple edges → Fin n for every n including zero, Sym2 edges and finite sets; reason: finite relabelling covers every source instance; loops are excluded in graphs and valid local configurations
--   - encoding: conditional on the exact accepted-edge history H_b → almost every history under its pushforward law, integrated against the explicit residual product law; reason: exact histories can have zero probability; Lemma 4.1 asserts measurability and disintegration, identifying this law as the conditional distribution
--   - encoding: expectations of finite vertex or edge counts → integrability is asserted in the conclusion together with the bound; reason: bounded measurable counts are integrable under the probability laws; this is an obligation, not an additional hypothesis
--   - encoding: conditioning further on the finite-valued background B → normalized restriction to {background=B} when its conditional mass is positive; reason: this is the genuine finite-event conditional law; zero-mass backgrounds impose no conditional obligation
--   - encoding: continuous arrival times with shadow matching at phase boundaries → strict prefixes, half-open reserve/retain phases and fixed sorting of tied times; reason: the phases agree with Algorithm 1; arrivals at any fixed boundary and ties have probability zero; the same convention is used throughout
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, STOC 2027 submission #1018 (October 2026), Lemma 2.2, p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1018.pdf

import Definitions.Def_FengLiYangMatching_General_Local

open MeasureTheory Finset
open scoped BigOperators

namespace FengLiYangMatching.General

theorem lemma_2_2 {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n)
    (hMG : M ⊆ graphEdges G) (hM : IsMatching M) (hmax : M.card = OPT G) (a b p : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 3/8)
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2/3) :
    ∀ᵐ h ∂historyLaw G b, ∀ e ∈ early a h, ∀ B : EdgeSet n,
      0 < conditionalLaw G b p h {w | background G a b h e w = B} →
      Integrable (coupledScore G M a b h e) (backgroundLaw G a b p h e B) ∧
      (∫ w, coupledScore G M a b h e w ∂backgroundLaw G a b p h e B)
        ≥ 3 * (references M h e).card := by sorry

end FengLiYangMatching.General
