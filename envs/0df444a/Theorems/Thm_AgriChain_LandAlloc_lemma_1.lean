-- Prove2me | Theorems.Thm_AgriChain_LandAlloc_lemma_1
-- name    : AgriChain.LandAlloc.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:52.183183+00:00
-- url     : https://prove2.me/theorems/1cc6eddf-75bb-414e-bcfd-a6195bc55db4
-- title:
--   Lemma 1, p. 14 — p̄₁ − p̄₂ depends on the total harvest only, is continuous, and changes sign at most once, from + to −
-- statement:
--   In the two-region agri-chain under its standing assumptions, let $\bar p_i(y_1,y_2)$ denote Processor $i$'s willingness to pay at harvests $y_1,y_2\ge0$, and put $D(T)=\bar p_1(T,0)-\bar p_2(T,0)$. Then:
--
--   1. the WTP difference depends on the harvests only through their total: $\bar p_1(y_1,y_2)-\bar p_2(y_1,y_2)=D(y_1+y_2)$;
--   2. $D$ is continuous on $[0,K_1+K_2]$;
--   3. $D(0)\ge0$;
--   4. once negative, $D$ stays negative: if $0\le T\le T'<K_1+K_2$ and $D(T)<0$, then $D(T')<0$.
--
--   Together these say that $\bar p_1-\bar p_2$ is continuous in $x_1Y^e_1+x_2Y^e_2$ and changes sign at most once, from "$+$" to "$-$", as the total harvest goes from $0$ to $K_1+K_2$. This identifies the harvest region in which each processor wins the price competition.
--
--   **Formalization Note.** Item 1 is the dependence through the total stated on p. 14, which "continuous in $x_1Y^e_1+x_2Y^e_2$" presupposes. Item 4 is stated on the half-open interval: at $T=K_1+K_2$ both WTPs equal $p_o$, so the difference returns to $0$ there.
-- source:
--   Li, Kouvelis & Dada, Agricultural Supply Chains in Emerging Markets: Competition and Cooperation under Correlated Yields, SSRN 3531158 (PDF of 2023-01-03), p. 14, Lemma 1

import Mathlib
import Definitions.Def_AgriChain_LandAlloc_Model

namespace AgriChain.LandAlloc

theorem lemma_1 (C : Chain) (hC : C.Standing) :
    (∀ y1 y2 : ℝ, 0 ≤ y1 → 0 ≤ y2 →
      wtp1 C y1 y2 - wtp2 C y1 y2 = wtp1 C (y1 + y2) 0 - wtp2 C (y1 + y2) 0) ∧
    ContinuousOn (fun T : ℝ => wtp1 C T 0 - wtp2 C T 0) (Set.Icc 0 (C.K1 + C.K2)) ∧
    0 ≤ wtp1 C 0 0 - wtp2 C 0 0 ∧
    ∀ T T' : ℝ, 0 ≤ T → T ≤ T' → T' < C.K1 + C.K2 →
      wtp1 C T 0 - wtp2 C T 0 < 0 → wtp1 C T' 0 - wtp2 C T' 0 < 0 := by sorry

end AgriChain.LandAlloc
