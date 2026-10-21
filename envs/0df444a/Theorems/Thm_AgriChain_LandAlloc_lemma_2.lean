-- Prove2me | Theorems.Thm_AgriChain_LandAlloc_lemma_2
-- name    : AgriChain.LandAlloc.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:11.970237+00:00
-- url     : https://prove2.me/theorems/1c99a1cf-bb23-42a0-902e-2354756cb1a5
-- title:
--   Lemma 2, p. 19 — if p^e − c < U/(hH), (0, 0) is the unique equilibrium
-- statement:
--   Consider the symmetric chain ($c_1=c_2=c$, $K_1=K_2=K>0$, $0\le p_o\le p^e-c$) with IID all-or-nothing yields, each equal to $H>0$ with probability $h\in(0,1)$, identical farmers ($U_1=U_2=U$, $A_1=A_2=A$) and land endowments $L_1,L_2\ge0$. If
--   $$p^e-c<\frac{U}{hH},$$
--   then $(x^*_1,x^*_2)=(0,0)$ is the unique equilibrium of the land-allocation game.
--
--   This is the no-production region of the paper's characterization: a farmer does not plant the export crop when its highest possible price, $p^e-c$, falls short of the per-unit cost $U$ adjusted by the success probability $h$ and the yield $H$. Its threshold is exactly the participation condition of Theorem 6.
--
--   **Formalization Note.** "Unique equilibrium" is stated as: a pair is an equilibrium if and only if it equals $(0,0)$; this asserts existence and uniqueness. The hypotheses $0<h<1$, $H>0$, $K>0$, $L_i\ge0$ are added to make the model well posed.
-- source:
--   Li, Kouvelis & Dada, Agricultural Supply Chains in Emerging Markets: Competition and Cooperation under Correlated Yields, SSRN 3531158 (PDF of 2023-01-03), p. 19, Lemma 2

import Mathlib
import Definitions.Def_AgriChain_LandAlloc_Model

namespace AgriChain.LandAlloc

theorem lemma_2 (pe po c K U A h H L1 L2 : ℝ) (hh : 0 < h ∧ h < 1) (hH : 0 < H) (hK : 0 < K)
    (hpo : 0 ≤ po ∧ po ≤ pe - c) (hL : 0 ≤ L1 ∧ 0 ≤ L2) (hmargin : pe - c < U / (h * H)) :
    ∀ x1 x2 : ℝ, IsEq (symChain pe po c K) (IID h H) U U A A L1 L2 x1 x2 ↔
      (x1 = 0 ∧ x2 = 0) := by sorry

end AgriChain.LandAlloc
