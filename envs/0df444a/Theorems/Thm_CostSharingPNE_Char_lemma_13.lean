-- Prove2me | Theorems.Thm_CostSharingPNE_Char_lemma_13
-- name    : CostSharingPNE.Char.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:27:48.980661+00:00
-- url     : https://prove2.me/theorems/87c17aec-165b-40f7-9d4b-0a6eec7e84f6
-- title:
--   Lemma 13, p. 56 — a universal weight system ω* with f^{W,T}_GWSV[ω^{W,T}] = f^T_GWSV[ω*] for every W ∈ 𝕎 and T ∈ 𝒯^W
-- statement:
--   Let $\mathbb W$ be a set of local welfare functions on $N=\{1,\dots,n\}$, $n>1$, and let $f^{\mathbb W}$ be budget-balanced distribution rules that guarantee equilibrium existence in all games $G\in\mathcal G(N,f^{\mathbb W},\mathbb W)$, where for each $W\in\mathbb W$
--   $$
--   f^W=\sum_{T\in\mathcal T^W} q^W_T\, f^{W,T}_{GWSV}[\omega^{W,T}] .
--   $$
--   Then there exists a weight system $\omega^*$ such that
--   $$
--   (\forall W\in\mathbb W)\ (\forall T\in\mathcal T^W)\qquad f^{W,T}_{GWSV}[\omega^{W,T}]=f^T_{GWSV}[\omega^*]. \tag{78}
--   $$
--
--   One weight system replaces all the coalition-wise weight systems, which with Lemmas 7 and 8 gives $f^W=f^W_{GWSV}[\omega^*]$ for every $W\in\mathbb W$ — the necessity half of Theorem 1 for budget-balanced rules.
--
--   **Formalization Note** The representation of $f^W$ is required at $i\in S$ (the shares that matter); (78) is an equality of the basis rules as functions of every $i$ and $S$.
-- source:
--   Gopalakrishnan, Marden, Wierman, arXiv:1402.3610v1, Lemma 13, (78), p. 56

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem
import Definitions.Def_CostSharingPNE_Char_Basis

namespace CostSharingPNE.Char

theorem lemma_13 (n : ℕ) (hn : 1 < n) (𝕎 : Set (Welfare n)) (f : Welfare n → Rule n)
    (hbb : ∀ W ∈ 𝕎, IsBudgetBalanced (f W) W) (hpne : GuaranteesPNE 𝕎 f)
    (Ω : Welfare n → Finset (Fin n) → WeightSystem n)
    (hΩ : ∀ W ∈ 𝕎, ∀ S : Finset (Fin n), ∀ i ∈ S,
      f W i S = ∑ T ∈ coalitions W, mobius W T * gwsvBasis (Ω W T) T i S) :
    ∃ ωstar : WeightSystem n, ∀ W ∈ 𝕎, ∀ T ∈ coalitions W,
      ∀ (i : Fin n) (S : Finset (Fin n)), gwsvBasis (Ω W T) T i S = gwsvBasis ωstar T i S := by sorry

end CostSharingPNE.Char
