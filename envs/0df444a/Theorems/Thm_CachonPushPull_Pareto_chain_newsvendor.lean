-- Prove2me | Theorems.Thm_CachonPushPull_Pareto_chain_newsvendor
-- name    : CachonPushPull.Pareto.chain_newsvendor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:23:54.866986+00:00
-- url     : https://prove2.me/theorems/689fa6a8-9037-4325-8c02-10d7c5753d3c
-- title:
--   Eqs. (1)–(2): the integrated chain's profit $\Pi(q)$ is concave, increasing on $[0,q^o]$ and maximized at $F(q^o) = (p-c)/(p-v)$
-- statement:
--   Let demand satisfy the standing assumptions (distribution function $F$ with $F(0) = 0$, strictly increasing on $[0,\infty)$, density $f$ on $(0,\infty)$, IGFR), and let $v < c < p$. The integrated supply chain's expected profit is
--   $$
--   \Pi(q) = (p - v) S(q) - (c - v) q, \qquad S(q) = q - \int_0^q F(x)\,dx .
--   $$
--   Then:
--
--   1. $\Pi$ is concave on $[0, \infty)$;
--   2. there is exactly one $q^o \in \mathbb R$ with $F(q^o) = \dfrac{p - c}{p - v}$;
--   3. for that $q^o$: $q^o > 0$, $\Pi$ attains its maximum over $[0,\infty)$ at $q^o$, and $\Pi$ is strictly increasing on $[0, q^o]$.
--
--   This is the newsvendor benchmark against which every contract is measured; $\Pi^o = \Pi(q^o)$ and the efficiency of a contract is $\Pi(q)/\Pi^o$.
--
--   **Formalization Note** Existence and uniqueness of $q^o$ are part of the statement, so later theorems may take $q^o$ as a parameter characterized by $F(q^o) = (p-c)/(p-v)$ without being vacuous. "Increasing" is read as strictly increasing, which is true because $F < F(q^o)$ on $[0, q^o)$.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 227, Eq. (1) and Eq. (2)

import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Model

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- Eqs. (1)–(2), p. 227: the integrated chain faces a newsvendor problem. -/
theorem chain_newsvendor (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) :
    ConcaveOn ℝ (Set.Ici 0) (chainProfit μ p c v) ∧
    (∃! qo : ℝ, cdf μ qo = (p - c) / (p - v)) ∧
    ∀ qo : ℝ, cdf μ qo = (p - c) / (p - v) →
      0 < qo ∧ IsMaxOn (chainProfit μ p c v) (Set.Ici 0) qo ∧
      StrictMonoOn (chainProfit μ p c v) (Set.Icc 0 qo) := by sorry

end CachonPushPull.Pareto
