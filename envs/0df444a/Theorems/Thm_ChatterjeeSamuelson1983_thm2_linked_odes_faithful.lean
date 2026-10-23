-- Prove2me | Theorems.Thm_ChatterjeeSamuelson1983_thm2_linked_odes_faithful
-- name    : ChatterjeeSamuelson1983.thm2_linked_odes_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:31:11.831067+00:00
-- url     : https://prove2.me/theorems/236be6b5-a8d2-4342-86ce-6bfdc9a65d23
-- title:
--   Theorem 2 (Chatterjee–Samuelson), as stated: (3a)–(3b) where the inverse offer functions are defined
-- statement:
--   Consider sealed-offer bargaining between a seller with reservation price $v_s \in [\underline v_s, \bar v_s]$ and a buyer with reservation price $v_b \in [\underline v_b, \bar v_b]$. Trade occurs iff the buyer's offer $b$ is at least the seller's ask $s$, at price $kb + (1-k)s$ with $0 \le k \le 1$. The buyer's belief about $v_s$ has distribution function $F_b$ with $F_b(\underline v_s) = 0$, $F_b(\bar v_s) = 1$, strictly increasing and differentiable on $[\underline v_s, \bar v_s]$ with density $f_b$. The seller's belief $F_s$ about $v_b$ has density $f_s$ and the same properties on $[\underline v_b, \bar v_b]$. Let $(S, B)$ be a Bayesian equilibrium in which both strategies are of class $A$: bounded, and strictly increasing and differentiable except possibly at the offer bounds. Then:
--
--   1. **(3a)** If $S$ is strictly increasing on an open interval $(a, c) \subseteq [\underline v_s, \bar v_s]$, $y \in (a, c)$, and $x = B^{-1}(S(y))$ is the unique buyer value with $B(x) = S(y)$, then
--   $$k F_b(y) S'(y) + f_b(y) S(y) = B^{-1}(S(y))\, f_b(y).$$
--   2. **(3b)** If $B$ is strictly increasing on an open interval $(a, c) \subseteq [\underline v_b, \bar v_b]$, $x \in (a, c)$, and $y = S^{-1}(B(x))$ is the unique seller value with $S(y) = B(x)$, then
--   $$(1-k)\bigl(1 - F_s(x)\bigr) B'(x) - f_s(x) B(x) = -S^{-1}(B(x))\, f_s(x).$$
--
--   This is Theorem 2 of Chatterjee and Samuelson (1983) as printed, with the inverse offer functions used only where they are defined. The existing theorem `ChatterjeeSamuelson.LinkedODE.linked_differential_equations` proves the same equations for every matching value, unique or not, so it implies this statement.
--
--   **Formalization Note** The inverses are not introduced as functions. The matching value is a bound variable, and the uniqueness hypothesis says that the paper's $B^{-1}(S(y))$ (resp. $S^{-1}(B(x))$) is defined. $S'(y)$ is `deriv S y`.
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Operations Research 31(5) (1983), doi:10.1287/opre.31.5.835, p. 840, Theorem 2, equations (3a)–(3b); class A definition p. 840; beliefs pp. 837–838

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_LinkedODE_RegularBelief
import Definitions.Def_ChatterjeeSamuelson_LinkedODE_ClassA
import Definitions.Def_ChatterjeeSamuelson_Shared_IsEquilibrium

open MeasureTheory ProbabilityTheory Set ChatterjeeSamuelson ChatterjeeSamuelson.LinkedODE

theorem ChatterjeeSamuelson1983.thm2_linked_odes_faithful (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (μb μs : Measure ℝ) (loS hiS loB hiB : ℝ) (fb fs S B : ℝ → ℝ)
    (hμb : RegularBelief μb loS hiS fb) (hμs : RegularBelief μs loB hiB fs)
    (hEq : Shared.IsEquilibrium k μb μs loS hiS loB hiB S B)
    (hS : ClassA S loS hiS) (hB : ClassA B loB hiB) :
    (∀ a c y : ℝ, loS ≤ a → c ≤ hiS → y ∈ Ioo a c → StrictMonoOn S (Ioo a c) →
      ∀ x ∈ Icc loB hiB, B x = S y → (∀ x' ∈ Icc loB hiB, B x' = S y → x' = x) →
        k * cdf μb y * deriv S y + fb y * S y = x * fb y) ∧
    (∀ a c x : ℝ, loB ≤ a → c ≤ hiB → x ∈ Ioo a c → StrictMonoOn B (Ioo a c) →
      ∀ y ∈ Icc loS hiS, S y = B x → (∀ y' ∈ Icc loS hiS, S y' = B x → y' = y) →
        (1 - k) * (1 - cdf μs x) * deriv B x - fs x * B x = -(y * fs x)) := by sorry
