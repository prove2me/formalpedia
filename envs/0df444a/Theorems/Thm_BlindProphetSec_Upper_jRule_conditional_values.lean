-- Prove2me | Theorems.Thm_BlindProphetSec_Upper_jRule_conditional_values
-- name    : BlindProphetSec.Upper.jRule_conditional_values
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:32:10.137165+00:00
-- url     : https://prove2.me/theorems/0fb1d8fc-7cef-4f26-a2bb-0df1bf488578
-- title:
--   §5, p. 19, first and second displays — the time-j rule's conditional values E(V_{σ_T} | σ_i = n + 1)
-- statement:
--   Fix $n\ge1$, $a\in[0,1]$ and $j\in\{1,\dots,n+1\}$, and run the time-$j$ rule on the §5 instance ($V_1,\dots,V_n$ equal $n$ with probability $1/n^2$ and $0$ otherwise, $V_{n+1}\equiv a$): accept a value $n$ whenever it appears, and accept $V_{n+1}$ if and only if it arrives at time $j$ or later. Let $T$ be its stopping time and $\sigma$ the uniform random order. Then for every position $i\in\{1,\dots,n+1\}$:
--
--   1. if $i\le j-1$,
--   $$\mathbb E(V_{\sigma_T}\mid \sigma_i = n+1) = n\Big[1-\Big(1-\frac1{n^2}\Big)^n\Big];$$
--   2. if $i\ge j$,
--   $$\mathbb E(V_{\sigma_T}\mid \sigma_i = n+1) = n\Big[1-\Big(1-\frac1{n^2}\Big)^{i-1}\Big] + \Big(1-\frac1{n^2}\Big)^{i-1} a.$$
--
--   Averaging these over the position $i$ of the constant variable gives the expected reward of the time-$j$ rule, the first line of the third display of §5.
--
--   **Formalization Note** The conditional expectation given $\sigma_i=n+1$ is written as $(n+1)\cdot\mathbb E(V_{\sigma_T}\mathbf 1_{\sigma_i=n+1})$, i.e. the sum over the $n!$ permutations placing $V_{n+1}$ at position $i$, divided by $n!$; no division by a probability occurs. Positions are 0-based in Lean (`i.val + 1` is the paper's $i$), and $V_{n+1}$ is `Fin.last n`.
-- source:
--   Correa, Saona & Ziliotto, Prophet Secretary Through Blind Strategies, arXiv:1807.07483v2, p. 19, §5, first and second displays

import Mathlib
import Definitions.Def_BlindProphetSec_Upper_Setting

open MeasureTheory Filter Topology

namespace BlindProphetSec.Upper

theorem jRule_conditional_values (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ n + 1) :
    (∀ i : Fin (n + 1), i.val + 1 < j →
      condValue (jRule n j) (hardLaw n a) i (Fin.last n) =
        ENNReal.ofReal ((n : ℝ) * (1 - (1 - 1 / (n : ℝ) ^ 2) ^ n))) ∧
    (∀ i : Fin (n + 1), j ≤ i.val + 1 →
      condValue (jRule n j) (hardLaw n a) i (Fin.last n) =
        ENNReal.ofReal ((n : ℝ) * (1 - (1 - 1 / (n : ℝ) ^ 2) ^ i.val) +
          (1 - 1 / (n : ℝ) ^ 2) ^ i.val * a)) := by sorry

end BlindProphetSec.Upper
