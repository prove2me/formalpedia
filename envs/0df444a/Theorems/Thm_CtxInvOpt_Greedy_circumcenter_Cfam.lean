-- Prove2me | Theorems.Thm_CtxInvOpt_Greedy_circumcenter_Cfam
-- name    : CtxInvOpt.Greedy.circumcenter_Cfam
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:30:26.370395+00:00
-- url     : https://prove2.me/theorems/be5d79a9-34e8-4174-9a8f-d834d48710de
-- title:
--   App-9, proof of Theorem 2, Step 1 — the unique circumcenter of C_{ε,ᾱ} is (1, ε, 0)/√(1+ε²)
-- statement:
--   Let $0<\bar\alpha<\pi/2$ and $0\le\varepsilon\le\tan\bar\alpha/2$, and let $C_{\varepsilon,\bar\alpha}\subseteq S^3$ be the set of the construction (the polyhedral cone cut out by $h_1'c\ge0$, $h_2'c\ge0$, $h_3'c\ge0$, intersected with the unit sphere). Then $C_{\varepsilon,\bar\alpha}$ has exactly one circumcenter, namely
--
--   $$\hat c(C_{\varepsilon,\bar\alpha})=\frac{1}{\sqrt{1+\varepsilon^2}}\,(1,\varepsilon,0).$$
--
--   That is, a unit vector $\hat c$ attains the uncertainty angle of $C_{\varepsilon,\bar\alpha}$ if and only if it equals this vector. It is the proxy cost the greedy circumcenter policy uses whenever its knowledge set is $C_{\varepsilon,\bar\alpha}$.
--
--   **Formalization Note** The page prints the unnormalized vector $(1,\varepsilon,0)$; a circumcenter lies on $S^3$, and Step 3 of the same proof (App-10) uses the normalized $(1,\varepsilon,0)/\sqrt{1+\varepsilon^2}$, which is what is stated. The statement is an equivalence, so it carries existence, uniqueness and the value.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, App-9, proof of Theorem 2, Step 1 (ĉ(C_{ε,ᾱ})); normalization from App-10, Step 3

import Mathlib
import Definitions.Def_CtxInvOpt_Offline_Geometry
import Definitions.Def_CtxInvOpt_Greedy_Family

open Real

namespace CtxInvOpt.Greedy

/-- **arXiv:2106.14015v3, App-9, proof of Theorem 2, Step 1.** For `0 < ᾱ < π/2` and
`0 ≤ ε ≤ tan ᾱ / 2`, the set `C_{ε,ᾱ}` has exactly one circumcenter, the unit vector
`(1, ε, 0)/√(1 + ε²)`. (The page prints the unnormalized `(1, ε, 0)`; Step 3, App-10, normalizes it.) -/
theorem circumcenter_Cfam {a ε : ℝ} (ha0 : 0 < a) (ha1 : a < π / 2) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ Real.tan a / 2) (chat : EuclideanSpace ℝ (Fin 3)) :
    CtxInvOpt.Offline.IsCircumcenter (Cfam ε a) chat ↔
      chat = (Real.sqrt (1 + ε ^ 2))⁻¹ • (!₂[1, ε, 0] : EuclideanSpace ℝ (Fin 3)) := by sorry

end CtxInvOpt.Greedy
