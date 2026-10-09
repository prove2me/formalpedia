-- Prove2me | Theorems.Thm_CostSharingPNE_Char_lemma_2
-- name    : CostSharingPNE.Char.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:25:46.49266+00:00
-- url     : https://prove2.me/theorems/88125f17-4212-4902-b289-46e2bca16c67
-- title:
--   Lemma 2, p. 20 — an equilibrium-guaranteeing budget-balanced rule gives zero to every noncontributing player
-- statement:
--   Let $W$ be a local welfare function on $N=\{1,\dots,n\}$, $n>1$, and let $f$ be a distribution rule that is budget-balanced for $W$ and guarantees the existence of a pure Nash equilibrium in all games $G\in\mathcal G(N,f,W)$. Then
--   $$
--   (\forall S\subseteq N)\quad(\forall i\in S-N(S))\qquad f(i,S)=0, \tag{18}
--   $$
--   where $N(S)=\bigcup\mathcal T(S)$ is the set of players of $S$ that belong to some contributing coalition contained in $S$.
--
--   The welfare $W(S)$ is distributed only among the contributing players of $S$; this generalizes Lemma 1.
-- source:
--   Gopalakrishnan, Marden, Wierman, arXiv:1402.3610v1, Lemma 2, (18), p. 20

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem
import Definitions.Def_CostSharingPNE_Char_Basis

namespace CostSharingPNE.Char

theorem lemma_2 (n : ℕ) (hn : 1 < n) (W : Welfare n) (f : Welfare n → Rule n)
    (hbb : IsBudgetBalanced (f W) W) (hpne : GuaranteesPNE {W} f) :
    ∀ S : Finset (Fin n), ∀ i ∈ S \ contributing W S, f W i S = 0 := by sorry

end CostSharingPNE.Char
