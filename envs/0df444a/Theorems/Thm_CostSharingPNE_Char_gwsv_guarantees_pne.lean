-- Prove2me | Theorems.Thm_CostSharingPNE_Char_gwsv_guarantees_pne
-- name    : CostSharingPNE.Char.gwsv_guarantees_pne
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:24:33.263737+00:00
-- url     : https://prove2.me/theorems/3155c00a-14b5-44d9-a0f6-9b8f39e33da4
-- title:
--   Appendix A, opening paragraph, p. 16 — generalized weighted Shapley value rules guarantee a pure Nash equilibrium in every game
-- statement:
--   Let $\omega$ be a weight system on the players $N=\{1,\dots,n\}$, $n>1$, let $\mathbb W$ be a set of local welfare functions, and let $g_{SV}$ be any map assigning to each $W\in\mathbb W$ a "ground" welfare function $g_{SV}(W)$. Use at every resource with welfare function $W$ the generalized weighted Shapley value rule of the ground welfare,
--   $$
--   f^W=f^{g_{SV}(W)}_{GWSV}[\omega].
--   $$
--   Then every game in $\mathcal G\bigl(N,\{f^{g_{SV}(W)}_{GWSV}[\omega]\}_{W\in\mathbb W},\mathbb W\bigr)$ (any number of resources, any assignment of welfare functions from $\mathbb W$ to resources, any nonempty action sets) has a pure Nash equilibrium.
--
--   This is the "if" direction of Theorem 1, which the paper attributes to Hart and Mas-Colell.
--
--   **Formalization Note** The weight system is the same for every $W\in\mathbb W$. The ground welfare $g_{SV}(W)$ is arbitrary, including its value on $\emptyset$.
-- source:
--   Gopalakrishnan, Marden, Wierman, arXiv:1402.3610v1, Appendix A, opening paragraph, p. 16 (citing Hart and Mas-Colell [18])

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem

namespace CostSharingPNE.Char

theorem gwsv_guarantees_pne (n : ℕ) (hn : 1 < n) (𝕎 : Set (Welfare n))
    (ω : WeightSystem n) (g : Welfare n → Welfare n) :
    GuaranteesPNE 𝕎 (fun W => gwsv ω (g W)) := by sorry

end CostSharingPNE.Char
