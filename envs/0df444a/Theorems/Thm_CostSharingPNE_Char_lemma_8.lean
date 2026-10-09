-- Prove2me | Theorems.Thm_CostSharingPNE_Char_lemma_8
-- name    : CostSharingPNE.Char.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:25:59.070987+00:00
-- url     : https://prove2.me/theorems/00fbd0ad-c500-4260-b890-72b17ab988ba
-- title:
--   Lemma 8, p. 32 — each basis rule f^T of an equilibrium-guaranteeing budget-balanced rule is a GWSV basis rule f^T_GWSV[ω^T]
-- statement:
--   Let $W$ be a local welfare function on $N=\{1,\dots,n\}$, $n>1$, and let $f$ be a distribution rule that is budget-balanced for $W$, satisfies $f(i,S)=0$ for $i\notin S$, and guarantees the existence of a pure Nash equilibrium in all games $G\in\mathcal G(N,f,W)$. Then for each basis distribution rule $f^T$ defined in (27), $T\in\mathcal T$, there exists a weight system $\omega^T$ such that
--   $$
--   f^T=f^T_{GWSV}[\omega^T] , \tag{51}
--   $$
--   where $f^T_{GWSV}[\omega](i,S)=\lambda_i/\sum_{j\in\overline T}\lambda_j$ if $i\in\overline T$ and $T\subseteq S$, and $0$ otherwise.
--
--   Combined with Lemma 7, $f$ is a combination of generalized weighted Shapley basis rules, possibly with a different weight system for each coalition.
--
--   **Formalization Note** The equality is of functions: for every player $i$ and every coalition $S$. The convention $f(i,S)=0$ off $S$ is the hypothesis `h0`.
-- source:
--   Gopalakrishnan, Marden, Wierman, arXiv:1402.3610v1, Lemma 8, (51), p. 32

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem
import Definitions.Def_CostSharingPNE_Char_Basis

namespace CostSharingPNE.Char

theorem lemma_8 (n : ℕ) (hn : 1 < n) (W : Welfare n) (f : Welfare n → Rule n)
    (hbb : IsBudgetBalanced (f W) W) (hpne : GuaranteesPNE {W} f)
    (h0 : ∀ i S, i ∉ S → f W i S = 0) :
    ∀ T ∈ coalitions W, ∃ ω : WeightSystem n,
      ∀ (i : Fin n) (S : Finset (Fin n)), basisRule (f W) W T i S = gwsvBasis ω T i S := by sorry

end CostSharingPNE.Char
