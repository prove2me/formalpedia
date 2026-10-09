-- Prove2me | Theorems.Thm_CostSharingPNE_Char_corollary_1
-- name    : CostSharingPNE.Char.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:27:16.656884+00:00
-- url     : https://prove2.me/theorems/94c06c3f-8b3d-4318-8f46-2a5aec3550e5
-- title:
--   Corollary 1 (inclusion–exclusion principle), p. 32 — integers n_T(T′) express q_T f^T(i, T) and q_T f^T(i, T − {j}) = 0 through f
-- statement:
--   Let $W$ be a local welfare function on $N=\{1,\dots,n\}$, $n>1$, and let $f$ be a distribution rule that is budget-balanced for $W$, satisfies $f(i,S)=0$ for $i\notin S$, and guarantees the existence of a pure Nash equilibrium in all games $G\in\mathcal G(N,f,W)$. Let $\{f^T\}_{T\in\mathcal T}$ be the basis rules defined in (27). Then for every $T\in\mathcal T$ there exist integers $\{n_T(T')\}_{T'\in\mathcal T}$ such that
--   $$
--   (\forall i\in T)\qquad q_T f^T(i,T)=\sum_{T'\in\mathcal T(T)} n_T(T')\,f(i,T') , \tag{49}
--   $$
--   $$
--   (\forall i\in T)\ (\forall j\in T-\{i\})\qquad 0=q_T f^T(i,T-\{j\})=\sum_{T'\in\mathcal T(T)} n_T(T')\,f(i,T'-\{j\}). \tag{50}
--   $$
--
--   The same integers serve every player $i$ and both identities. The corollary isolates a single basis share as an integer combination of shares of $f$, which is what lets the counterexamples of Appendix A target one basis rule.
--
--   **Formalization Note** The integers are a function `c : Finset (Fin n) → ℤ` chosen once per $T$, before the quantifiers over $i$ and $j$. The convention $f(i,S)=0$ off $S$ is the hypothesis `h0`.
-- source:
--   Gopalakrishnan, Marden, Wierman, arXiv:1402.3610v1, Corollary 1, (49)–(50), p. 32

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem
import Definitions.Def_CostSharingPNE_Char_Basis

namespace CostSharingPNE.Char

theorem corollary_1 (n : ℕ) (hn : 1 < n) (W : Welfare n) (f : Welfare n → Rule n)
    (hbb : IsBudgetBalanced (f W) W) (hpne : GuaranteesPNE {W} f)
    (h0 : ∀ i S, i ∉ S → f W i S = 0) :
    ∀ T ∈ coalitions W, ∃ c : Finset (Fin n) → ℤ,
      (∀ i ∈ T, mobius W T * basisRule (f W) W T i T =
          ∑ T' ∈ coalitionsIn W T, (c T' : ℝ) * f W i T') ∧
      (∀ i ∈ T, ∀ j ∈ T, j ≠ i →
          0 = mobius W T * basisRule (f W) W T i (T.erase j) ∧
          mobius W T * basisRule (f W) W T i (T.erase j) =
            ∑ T' ∈ coalitionsIn W T, (c T' : ℝ) * f W i (T'.erase j)) := by sorry

end CostSharingPNE.Char
