-- Prove2me | Theorems.Thm_AgriChain_LandAlloc_theorem_6
-- name    : AgriChain.LandAlloc.theorem_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:09.876389+00:00
-- url     : https://prove2.me/theorems/7d1e4d95-6e5f-4ef0-aa92-6f72d0ba60c2
-- title:
--   Theorem 6 parts 1, 3, 4, p. 20 — under IID all-or-nothing yields, p_o selects a continuum on x₁+x₂=K/H, the unique (K/H, K/H), or the unique (2K/H, 2K/H)
-- statement:
--   Consider the symmetric agri-chain: two identical processors with unit processing cost $c$ and capacity $K>0$, world price $p^e$ and minimum guaranteed price $p_o$ with $0\le p_o\le p^e-c$; two identical farmers with per-unit land cost $U>0$, constant $A$ and land endowments $L_1,L_2\ge 2K/H$; and IID all-or-nothing yields, each farmer's yield being $H>0$ with probability $h\in(0,1)$ and $0$ otherwise. Assume the participation condition
--   $$p^e-c>\frac{U}{hH}.$$
--   Then the equilibria $(x^*_1,x^*_2)$ of the land-allocation game are as follows.
--
--   1. **Under-production.** If $p_o<\dfrac{U}{h^2H}-\dfrac{1-h}{h}(p^e-c)$, every equilibrium satisfies $x^*_1+x^*_2=K/H$, and there is a continuum of equilibria: a nondegenerate segment $\{(t,K/H-t): a\le t\le b\}$, $a<b$, consists of equilibria.
--   2. **Full production.** If $\dfrac{2h-1}{2h}(p^e-c)+\dfrac{U}{2h^2H}\le p_o<\dfrac12\Big[(p^e-c)+\dfrac{U}{h(1-h)H}\Big]$, then $(K/H,K/H)$ is the unique equilibrium.
--   3. **Over-production.** If $p_o>\dfrac12\Big[(p^e-c)+\dfrac{U}{h(1-h)H}\Big]$, then $(2K/H,2K/H)$ is the unique equilibrium.
--
--   The minimum guaranteed price thus selects between under-, full- and over-production of the export crop relative to the total processing capacity $2K$; this is the paper's main characterization of the land-allocation game.
--
--   **Formalization Note.** The items above are parts 1, 3 and 4 of the paper's Theorem 6. Part 2 ("zero or one equilibrium with $x^*_1+x^*_2\in[3K/(2H),2K/H)$") is not posed: it is false as printed, since at $h=1/2$, $H=K=U=1$, $p^e-c=5$, $p_o=0$ its hypotheses hold but the unique equilibrium is $(4/5,3/5)$, with total $7/5<3K/(2H)$. Two thresholds are made strict: the participation condition (printed "$\ge$"), because at $p^e-c=U/(hH)$ the pair $(0,0)$ is also an equilibrium and part 1 fails; and the over-production threshold of part 4 (printed "$\ge$"), because at equality every point of $[K/H,2K/H]^2$ is an equilibrium. The hypotheses $0<h<1$, $H,K,U>0$ (the thresholds divide by $h$, $H$ and $h(1-h)$) and $L_i\ge 2K/H$ (the over-production equilibrium plants $2K/H$) are added. "Unique equilibrium" is stated as an "if and only if", asserting existence and uniqueness. The equilibrium is that of the full model, with the WTPs defined as suprema and the final prices of Theorem 3.
-- source:
--   Li, Kouvelis & Dada, Agricultural Supply Chains in Emerging Markets: Competition and Cooperation under Correlated Yields, SSRN 3531158 (PDF of 2023-01-03), pp. 19–20, §3.1, Theorem 6 parts 1, 3, 4

import Mathlib
import Definitions.Def_AgriChain_LandAlloc_Model

namespace AgriChain.LandAlloc

theorem theorem_6 (pe po c K U A h H L1 L2 : ℝ)
    (hh : 0 < h ∧ h < 1) (hH : 0 < H) (hK : 0 < K) (hU : 0 < U)
    (hpo : 0 ≤ po ∧ po ≤ pe - c) (hL : 2 * K / H ≤ L1 ∧ 2 * K / H ≤ L2)
    (hpart : U / (h * H) < pe - c) :
    -- part 1: under-production, a continuum of equilibria on x₁ + x₂ = K/H
    (po < U / (h ^ 2 * H) - (1 - h) / h * (pe - c) →
      (∀ x1 x2 : ℝ, IsEq (symChain pe po c K) (IID h H) U U A A L1 L2 x1 x2 →
        x1 + x2 = K / H) ∧
      ∃ a b : ℝ, a < b ∧ ∀ t ∈ Set.Icc a b,
        IsEq (symChain pe po c K) (IID h H) U U A A L1 L2 t (K / H - t)) ∧
    -- part 3: full production, (K/H, K/H) is the unique equilibrium
    ((2 * h - 1) / (2 * h) * (pe - c) + U / (2 * h ^ 2 * H) ≤ po →
      po < ((pe - c) + U / (h * (1 - h) * H)) / 2 →
      ∀ x1 x2 : ℝ, IsEq (symChain pe po c K) (IID h H) U U A A L1 L2 x1 x2 ↔
        (x1 = K / H ∧ x2 = K / H)) ∧
    -- part 4: over-production, (2K/H, 2K/H) is the unique equilibrium (strict threshold)
    (((pe - c) + U / (h * (1 - h) * H)) / 2 < po →
      ∀ x1 x2 : ℝ, IsEq (symChain pe po c K) (IID h H) U U A A L1 L2 x1 x2 ↔
        (x1 = 2 * K / H ∧ x2 = 2 * K / H)) := by sorry

end AgriChain.LandAlloc
