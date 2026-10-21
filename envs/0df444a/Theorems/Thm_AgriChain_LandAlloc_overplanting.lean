-- Prove2me | Theorems.Thm_AgriChain_LandAlloc_overplanting
-- name    : AgriChain.LandAlloc.overplanting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:09.814859+00:00
-- url     : https://prove2.me/theorems/6a1a7061-9237-463f-803c-6e8836688a27
-- title:
--   §3.1, p. 19 — F_i decreases at rate U beyond 2K/H, so every equilibrium has x∗_i ≤ 2K/H
-- statement:
--   Consider the symmetric chain ($c_1=c_2=c$, $K_1=K_2=K>0$, $0\le p_o\le p^e-c$) with IID all-or-nothing yields, each equal to $H>0$ with probability $h\in(0,1)$, and identical farmers ($U_1=U_2=U$, $A_1=A_2=A$). Then:
--
--   1. beyond $2K/H$ farmer 1's profit decreases at rate $U$: for $x_1\ge 2K/H$ and $x_2\ge0$,
--   $$F_1(x_1,x_2)=F_1\!\left(\tfrac{2K}{H},x_2\right)-U\left(x_1-\tfrac{2K}{H}\right);$$
--   2. the same holds for farmer 2: for $x_1\ge0$ and $x_2\ge2K/H$, $F_2(x_1,x_2)=F_2\!\left(x_1,\tfrac{2K}{H}\right)-U\left(x_2-\tfrac{2K}{H}\right)$;
--   3. if $U>0$, then for any land endowments $L_1,L_2$ every equilibrium $(x^*_1,x^*_2)$ satisfies $x^*_1\le 2K/H$ and $x^*_2\le 2K/H$.
--
--   This restricts the search for equilibria to $[0,2K/H]^2$, as in the paper's analysis of identical regions.
--
--   **Formalization Note.** The paper's "$\partial F_i/\partial x_i=-U$ for $x_i>2K/H$" is stated in integrated form, which also covers the kink at $2K/H$. Item 3 needs $U>0$ (added): with $U=0$ any over-planting is also optimal.
-- source:
--   Li, Kouvelis & Dada, Agricultural Supply Chains in Emerging Markets: Competition and Cooperation under Correlated Yields, SSRN 3531158 (PDF of 2023-01-03), p. 19, §3.1

import Mathlib
import Definitions.Def_AgriChain_LandAlloc_Model

namespace AgriChain.LandAlloc

theorem overplanting (pe po c K U A h H : ℝ) (hh : 0 < h ∧ h < 1) (hH : 0 < H) (hK : 0 < K)
    (hpo : 0 ≤ po ∧ po ≤ pe - c) :
    (∀ x1 x2 : ℝ, 2 * K / H ≤ x1 → 0 ≤ x2 →
      F1 (symChain pe po c K) (IID h H) U A x1 x2 =
        F1 (symChain pe po c K) (IID h H) U A (2 * K / H) x2 - U * (x1 - 2 * K / H)) ∧
    (∀ x1 x2 : ℝ, 0 ≤ x1 → 2 * K / H ≤ x2 →
      F2 (symChain pe po c K) (IID h H) U A x1 x2 =
        F2 (symChain pe po c K) (IID h H) U A x1 (2 * K / H) - U * (x2 - 2 * K / H)) ∧
    (0 < U → ∀ L1 L2 x1 x2 : ℝ,
      IsEq (symChain pe po c K) (IID h H) U U A A L1 L2 x1 x2 →
        x1 ≤ 2 * K / H ∧ x2 ≤ 2 * K / H) := by sorry

end AgriChain.LandAlloc
