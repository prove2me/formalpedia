-- Prove2me | Theorems.Thm_CostSharingPNE_Char_lemma_7
-- name    : CostSharingPNE.Char.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:25:38.919109+00:00
-- url     : https://prove2.me/theorems/5b36bd69-6f50-4a95-8b5f-d84626d8a028
-- title:
--   Lemma 7, p. 28 — an equilibrium-guaranteeing budget-balanced rule is the combination f = Σ_T q_T f^T of its basis rules (41)
-- statement:
--   Let $W$ be a local welfare function on $N=\{1,\dots,n\}$, $n>1$, and let $f$ be a distribution rule that is budget-balanced for $W$, satisfies $f(i,S)=0$ for $i\notin S$, and guarantees the existence of a pure Nash equilibrium in all games $G\in\mathcal G(N,f,W)$. Then the basis distribution rules $\{f^T\}_{T\in\mathcal T}$ defined in (27) satisfy
--   $$
--   (\forall S\subseteq N)\ (\forall i\in S)\qquad f(i,S)=\sum_{T\in\mathcal T} q_T\, f^T(i,S). \tag{41}
--   $$
--
--   This is the basis representation (4) of $f$, step (c) of the decomposition; the paper notes that not every rule has such a representation, but every equilibrium-guaranteeing one does.
--
--   **Formalization Note** The convention $f(i,S)=0$ off $S$ (p. 4) is the hypothesis `h0`, needed because (27) reads $f(i,T)$ for $i\notin T$.
-- source:
--   Gopalakrishnan, Marden, Wierman, arXiv:1402.3610v1, Lemma 7, (41), p. 28

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem
import Definitions.Def_CostSharingPNE_Char_Basis

namespace CostSharingPNE.Char

theorem lemma_7 (n : ℕ) (hn : 1 < n) (W : Welfare n) (f : Welfare n → Rule n)
    (hbb : IsBudgetBalanced (f W) W) (hpne : GuaranteesPNE {W} f)
    (h0 : ∀ i S, i ∉ S → f W i S = 0) :
    ∀ S : Finset (Fin n), ∀ i ∈ S,
      f W i S = ∑ T ∈ coalitions W, mobius W T * basisRule (f W) W T i S := by sorry

end CostSharingPNE.Char
