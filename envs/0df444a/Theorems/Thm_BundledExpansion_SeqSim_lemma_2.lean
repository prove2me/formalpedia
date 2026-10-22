-- Prove2me | Theorems.Thm_BundledExpansion_SeqSim_lemma_2
-- name    : BundledExpansion.SeqSim.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:08.090546+00:00
-- url     : https://prove2.me/theorems/8ac40d84-0824-4d29-99a1-520277ad8031
-- title:
--   Lemma 2, p. 13 — simultaneous cycle costs
-- statement:
--   In a feasible cycle $[s,e]$ with $K=m+1$ joint replenishments at times $\tau_k$, let $\beta\in[1,2]$ be the joint fixed-cost multiplier. The fixed and purchase costs are $\beta A K$ and the same purchase expression as in Lemma 1. The holding cost is
--
--   $$
--   \sum_{i=1}^{2}h_i\left[\sum_{k=1}^{K}(\tau_{k+1}-\tau_k)D_i(s,\tau_{k+1})-F_i(s,e)\right].
--   $$
--
--   These formulas put the two policies on a common cost basis. **Formalization Note** The Lean cycle’s count $K$ is the paper’s $m+1$; indices 0 and 1 are the paper’s 1 and 2. Demand continuity supplies integrability of the holding-cost trajectory.
-- source:
--   Arbabian, Chen & Moinzadeh, Capacity Expansions with Bundled Supplies of Attributes, SSRN 3085349 (manuscript of April 14, 2019), https://ssrn.com/abstract=3085349, p. 13 (PDF 14), Lemma 2, equations (6)–(7)

import Mathlib
import Definitions.Def_BundledExpansion_SeqSim_Model

namespace BundledExpansion.SeqSim

theorem lemma_2 (P : Params) (hS : P.Standing) (hR : P.Regular)
    (β : ℝ) (hβ : β ∈ Set.Icc (1 : ℝ) 2)
    (C : SimCycle) (hC : C.Valid P) :
    C.fixed P β = β * P.A * C.K ∧
    purchase P (C.plan P) = commonPurchase P C.start C.stop ∧
    holding P (C.plan P) C.start C.stop =
      ∑ i : Fin 2, P.h i *
        ((∑ k ∈ Finset.range C.K,
          (C.τ (k + 1) - C.τ k) * D P i C.start (C.τ (k + 1))) -
          F P i C.start C.stop) := by sorry

end BundledExpansion.SeqSim
