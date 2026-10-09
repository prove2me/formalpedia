-- Prove2me | Theorems.Thm_CostSharingPNE_Char_lemma_5
-- name    : CostSharingPNE.Char.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:25:55.966008+00:00
-- url     : https://prove2.me/theorems/bfae9622-b470-42f9-892a-484b6604a6f3
-- title:
--   Lemma 5, p. 26 — each basis rule f^T of a budget-balanced rule, built by (27), is budget-balanced for the inclusion function W^T
-- statement:
--   Let $W$ be a welfare function on $N=\{1,\dots,n\}$, $n>1$, and let $f$ be a distribution rule that is budget-balanced for $W$, with the convention $f(i,S)=0$ for $i\notin S$. Let $\{f^T\}_{T\in\mathcal T}$ be the basis distribution rules defined from $f$ by the recursion (27). Then each $f^T$ is budget-balanced for the inclusion function $W^T$:
--   $$
--   (\forall T\in\mathcal T)\ (\forall S\subseteq N)\qquad \sum_{i\in S} f^T(i,S)=W^T(S).
--   $$
--
--   No equilibrium hypothesis is needed. The lemma is step (b) of the decomposition of $f$ into basis rules.
--
--   **Formalization Note** The recursion (27) evaluates $f(i,T)$ also for $i\notin T$, so the paper's convention $f(i,S):=0$ for $i\notin S$ (p. 4) is carried as the hypothesis `h0`.
-- source:
--   Gopalakrishnan, Marden, Wierman, arXiv:1402.3610v1, Lemma 5, p. 26; recursion (27), p. 24

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem
import Definitions.Def_CostSharingPNE_Char_Basis

namespace CostSharingPNE.Char

theorem lemma_5 (n : ℕ) (hn : 1 < n) (W : Welfare n) (g : Rule n)
    (hbb : IsBudgetBalanced g W) (h0 : ∀ i S, i ∉ S → g i S = 0) :
    ∀ T ∈ coalitions W, ∀ S : Finset (Fin n),
      ∑ i ∈ S, basisRule g W T i S = unanimity T S := by sorry

end CostSharingPNE.Char
