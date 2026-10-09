-- Prove2me | Theorems.Thm_CostSharingPNE_Char_lemma_1
-- name    : CostSharingPNE.Char.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:25:42.864638+00:00
-- url     : https://prove2.me/theorems/fccdd17f-5111-4634-a38f-56c561c7859d
-- title:
--   Lemma 1, p. 19 — if no contributing coalition forms in S, an equilibrium-guaranteeing budget-balanced rule gives every player of S zero
-- statement:
--   Let $W$ be a local welfare function on $N=\{1,\dots,n\}$, $n>1$, and let $f$ be a distribution rule that is budget-balanced for $W$ and guarantees the existence of a pure Nash equilibrium in all games $G\in\mathcal G(N,f,W)$. Then
--   $$
--   (\forall S\subseteq N \text{ with } \mathcal T(S)=\emptyset)\quad(\forall i\in S)\qquad f(i,S)=0. \tag{17}
--   $$
--   Here $\mathcal T(S)$ is the set of contributing coalitions of $W$ contained in $S$.
--
--   This is the first of three necessary conditions (Proposition 8): a coalition containing no contributing coalition receives nothing.
--
--   **Formalization Note** "All games in $\mathcal G(N,f,W)$" is `GuaranteesPNE {W} f`: every game whose resources all carry $W$.
-- source:
--   Gopalakrishnan, Marden, Wierman, arXiv:1402.3610v1, Lemma 1, (17), p. 19

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem
import Definitions.Def_CostSharingPNE_Char_Basis

namespace CostSharingPNE.Char

theorem lemma_1 (n : ℕ) (hn : 1 < n) (W : Welfare n) (f : Welfare n → Rule n)
    (hbb : IsBudgetBalanced (f W) W) (hpne : GuaranteesPNE {W} f) :
    ∀ S : Finset (Fin n), coalitionsIn W S = ∅ → ∀ i ∈ S, f W i S = 0 := by sorry

end CostSharingPNE.Char
