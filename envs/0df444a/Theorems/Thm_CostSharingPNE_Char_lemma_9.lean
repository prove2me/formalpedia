-- Prove2me | Theorems.Thm_CostSharingPNE_Char_lemma_9
-- name    : CostSharingPNE.Char.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:25:51.275208+00:00
-- url     : https://prove2.me/theorems/b4f3c778-7ed4-435e-b742-238eed982573
-- title:
--   Lemma 9 (global consistency), p. 35 — f^{1,T′}(i, T′) f^{2,T}(j, T) = f^{2,T}(i, T) f^{1,T′}(j, T′) for T′ ∈ 𝒯¹_ij, T ∈ 𝒯²_ij
-- statement:
--   Let $W_1,W_2$ be two local welfare functions on $N=\{1,\dots,n\}$, $n>1$, and let $f^1=f^{W_1}$, $f^2=f^{W_2}$ be corresponding distribution rules, budget-balanced for $W_1$ and $W_2$ respectively and vanishing off the sharing coalition, that guarantee equilibrium existence in all games $G\in\mathcal G(N,\{f^1,f^2\},\{W_1,W_2\})$. Write $f^{1,T}$ and $f^{2,T}$ for their basis rules (27), so that $f^1=\sum_{T\in\mathcal T^1}q^1_Tf^{1,T}$ and $f^2=\sum_{T\in\mathcal T^2}q^2_Tf^{2,T}$. Then for any two players $i,j\in N$ and any two coalitions $T'\in\mathcal T^1_{ij}$ and $T\in\mathcal T^2_{ij}$,
--   $$
--   f^{1,T'}(i,T')\,f^{2,T}(j,T)=f^{2,T}(i,T)\,f^{1,T'}(j,T'). \tag{52}
--   $$
--
--   The ratio of the shares of $i$ and $j$ is therefore the same in every coalition containing both, across both welfare functions. The case $W_1=W_2$ is included and gives consistency across the coalitions of a single welfare function.
--
--   **Formalization Note** The rules are `f W₁` and `f W₂` of one family `f`, with the convention $f(i,S)=0$ off $S$ for both (`h0₁`, `h0₂`), needed by (27).
-- source:
--   Gopalakrishnan, Marden, Wierman, arXiv:1402.3610v1, Lemma 9, (52), p. 35

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem
import Definitions.Def_CostSharingPNE_Char_Basis

namespace CostSharingPNE.Char

theorem lemma_9 (n : ℕ) (hn : 1 < n) (W₁ W₂ : Welfare n) (f : Welfare n → Rule n)
    (hbb₁ : IsBudgetBalanced (f W₁) W₁) (hbb₂ : IsBudgetBalanced (f W₂) W₂)
    (h0₁ : ∀ i S, i ∉ S → f W₁ i S = 0) (h0₂ : ∀ i S, i ∉ S → f W₂ i S = 0)
    (hpne : GuaranteesPNE {W₁, W₂} f) :
    ∀ i j : Fin n, ∀ T' ∈ coalitionsPair W₁ i j, ∀ T ∈ coalitionsPair W₂ i j,
      basisRule (f W₁) W₁ T' i T' * basisRule (f W₂) W₂ T j T =
        basisRule (f W₂) W₂ T i T * basisRule (f W₁) W₁ T' j T' := by sorry

end CostSharingPNE.Char
