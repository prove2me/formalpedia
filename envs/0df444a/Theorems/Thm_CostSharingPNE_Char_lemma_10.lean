-- Prove2me | Theorems.Thm_CostSharingPNE_Char_lemma_10
-- name    : CostSharingPNE.Char.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:25:54.50936+00:00
-- url     : https://prove2.me/theorems/12704163-931c-48a4-bb0e-36c5a32c4911
-- title:
--   Lemma 10 (cyclic consistency), p. 42 — around a cycle of minimal positive-share coalitions, ∏ f^{j,T_j}(i_j, T_j) = ∏ f^{j,T_j}(i_{j+1}, T_j)
-- statement:
--   Let $k\ge3$ be an integer and $W_1,\dots,W_k$ local welfare functions on $N=\{1,\dots,n\}$, $n>1$. Let $f^j=\sum_{T\in\mathcal T^j}q^j_Tf^{j,T}$ ($j=1,\dots,k$) be corresponding budget-balanced distribution rules, vanishing off the sharing coalition, that guarantee equilibrium existence in all games $G\in\mathcal G(N,\{f^1,\dots,f^k\},\{W_1,\dots,W_k\})$, where $f^{j,T}$ are the basis rules (27). Let $i_1,\dots,i_k\in N$ be players such that there are coalitions
--   $$
--   T_1\in\bigl(\mathcal T^{1+}_{i_1i_2}\bigr)^{\min},\ T_2\in\bigl(\mathcal T^{2+}_{i_2i_3}\bigr)^{\min},\ \dots,\ T_k\in\bigl(\mathcal T^{k+}_{i_ki_1}\bigr)^{\min},
--   $$
--   where $\mathcal T^{j+}_{xy}$ is the set of coalitions of $\mathcal T^j_{xy}$ in which $x$ or $y$ gets a positive basis share (53). Then
--   $$
--   f^{1,T_1}(i_1,T_1)\,f^{2,T_2}(i_2,T_2)\cdots f^{k,T_k}(i_k,T_k)=f^{1,T_1}(i_2,T_1)\,f^{2,T_2}(i_3,T_2)\cdots f^{k,T_k}(i_1,T_k). \tag{65}
--   $$
--
--   Lemma 9 compares two coalitions; this lemma rules out inconsistent cycles of length three or more, which is what allows a single weight system to be assembled.
--
--   **Formalization Note** Indices are cyclic: player $i_{j+1}$ is `p (finRotate k l)`, so the last coalition pairs $i_k$ with $i_1$. The players need not be distinct and the welfare functions may repeat. The convention $f(i,S)=0$ off $S$ is the hypothesis `h0`.
-- source:
--   Gopalakrishnan, Marden, Wierman, arXiv:1402.3610v1, Lemma 10, (65), p. 42; (53), p. 35

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem
import Definitions.Def_CostSharingPNE_Char_Basis

namespace CostSharingPNE.Char

theorem lemma_10 (n : ℕ) (hn : 1 < n) (k : ℕ) (hk : 3 ≤ k) (W : Fin k → Welfare n)
    (f : Welfare n → Rule n)
    (hbb : ∀ l, IsBudgetBalanced (f (W l)) (W l))
    (h0 : ∀ l i S, i ∉ S → f (W l) i S = 0)
    (hpne : GuaranteesPNE (Set.range W) f)
    (p : Fin k → Fin n) (T : Fin k → Finset (Fin n))
    (hT : ∀ l, T l ∈ minimals (plusPair (f (W l)) (W l) (p l) (p (finRotate k l)))) :
    ∏ l, basisRule (f (W l)) (W l) (T l) (p l) (T l) =
      ∏ l, basisRule (f (W l)) (W l) (T l) (p (finRotate k l)) (T l) := by sorry

end CostSharingPNE.Char
