-- Prove2me | Theorems.Thm_FengLiYangMatching_General_Supplement_lemma_B_2
-- name    : FengLiYangMatching.General.Supplement.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:22:10.119354+00:00
-- url     : https://prove2.me/theorems/2c1e0e7c-ed19-415e-b8a6-7e0849a1130f
-- title:
--   Lemma B.2 — Triangle-free coupled comparison
-- statement:
--   Use Algorithm 1 with $a=3/32$, $b=4/11$, and $p=11/25$ on any finite triangle-free simple graph $G$. Fix a maximum matching $M^*$. For almost every shadow history $H_b$, each reserve-phase shadow edge $e$, and every background value $B$ of positive conditional probability, the coupled score is integrable and
--
--   $$\mathbb E[7N+4R+3K\mid H_b,B]\ge7k_e.$$
--
--   Here $N$ counts matched endpoints of $e$ in $M(B_e)$; $R,K$ count its reference vertices matched in $M(B_e),M(B)$; and $k_e$ is its number of reference vertices. This comparison supplies the recovery bound for Theorem 1.2.
--
--   Differences from the source:
--   - encoding: arbitrary finite labelled vertex set → Fin n and unordered Sym2 edges, for every natural n; reason: every finite simple graph has such a labelling; the representation removes no instance
--   - encoding: conditioning on H_b and B → almost every history under historyLaw, followed by backgroundLaw on each positive-mass background event, with integrability explicit; reason: exact histories can have probability zero; the published conditional experiments implement the source conditioning
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, Improved Bounds for Online Matching with Random Edge Arrivals, STOC 2027 submission #1018 (October 2026), Lemma B.2, p. 26.

import Definitions.Def_FengLiYangMatching_General_Supplement_Score

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace FengLiYangMatching.General.Supplement

theorem lemma_B_2 {n : ℕ} (G : SimpleGraph (Fin n)) (htf : G.CliqueFree 3)
    (M : EdgeSet n) (hMG : M ⊆ graphEdges G) (hM : IsMatching M)
    (hmax : M.card = OPT G) :
    ∀ᵐ h ∂historyLaw G (4/11), ∀ e ∈ early (3/32) h, ∀ B : EdgeSet n,
      0 < conditionalLaw G (4/11) (11/25) h
        {w | background G (3/32) (4/11) h e w = B} →
      Integrable (triangleScore G M (3/32) (4/11) h e)
        (backgroundLaw G (3/32) (4/11) (11/25) h e B) ∧
      (∫ w, triangleScore G M (3/32) (4/11) h e w
        ∂backgroundLaw G (3/32) (4/11) (11/25) h e B)
        ≥ 7 * (references M h e).card := by sorry

end FengLiYangMatching.General.Supplement
