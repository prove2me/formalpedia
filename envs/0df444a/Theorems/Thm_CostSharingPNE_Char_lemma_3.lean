-- Prove2me | Theorems.Thm_CostSharingPNE_Char_lemma_3
-- name    : CostSharingPNE.Char.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:26:23.594596+00:00
-- url     : https://prove2.me/theorems/a360c144-eeb8-41b1-881e-c94383cca8c4
-- title:
--   Lemma 3, p. 21 — an equilibrium-guaranteeing budget-balanced rule shares as if the noncontributing players were absent: f(i, S) = f(i, N(S))
-- statement:
--   Let $W$ be a local welfare function on $N=\{1,\dots,n\}$, $n>1$, and let $f$ be a distribution rule that is budget-balanced for $W$ and guarantees the existence of a pure Nash equilibrium in all games $G\in\mathcal G(N,f,W)$. Then
--   $$
--   (\forall S\subseteq N)\quad(\forall i\in N(S))\qquad f(i,S)=f(i,N(S)), \tag{20}
--   $$
--   where $N(S)$ is the set of contributing players of $S$.
--
--   Together with Lemma 2 this is Proposition 8: $f(i,S)=f(i,N(S))$ for every $i\in S$.
-- source:
--   Gopalakrishnan, Marden, Wierman, arXiv:1402.3610v1, Lemma 3, (20), p. 21

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem
import Definitions.Def_CostSharingPNE_Char_Basis

namespace CostSharingPNE.Char

theorem lemma_3 (n : ℕ) (hn : 1 < n) (W : Welfare n) (f : Welfare n → Rule n)
    (hbb : IsBudgetBalanced (f W) W) (hpne : GuaranteesPNE {W} f) :
    ∀ S : Finset (Fin n), ∀ i ∈ contributing W S,
      f W i S = f W i (contributing W S) := by sorry

end CostSharingPNE.Char
