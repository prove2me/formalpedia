-- Prove2me | Theorems.Thm_BayesClock_uniform_price_welfare
-- name    : BayesClock.uniform_price_welfare
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:13:56.860471+00:00
-- url     : https://prove2.me/theorems/0288a72b-0ca6-4674-aa58-1c6ee0938b55
-- title:
--   Section 3.2 note: $W(p)$ is the expected welfare of a uniform-price clock auction
-- statement:
--   For a downward-closed constraint, independent values and any price $p$, there is a single-price clock auction posting $p$ to every bidder whose expected welfare equals
--
--   $$\mathbb E\Big[\max_{S\in\mathcal S}\sum_{i\in S}\mathbb E[v_i\mid v_i\ge p]\cdot\mathbb I[v_i\ge p]\Big].$$
--
--   The identity turns Lemma 3 into a statement about an actual auction: the selection rule sees only who stayed, and can use conditional means of those bidders.
--
--   Differences from the source:
--   - encoding: a single-price clock auction with a uniform price p (rule implicit) → there exists a SinglePriceAuction with constant price p; reason: the paper leaves the selection rule implicit; existence is what its later use needs
--   - encoding: values are amounts a buyer is willing to pay, with expectations written E → values in ℝ≥0, expectations as ℝ≥0∞-valued lower integrals; reason: the proof starts every integral at 0 and a bidder pays nothing by leaving; a lower integral agrees with the expectation of a nonnegative value
--   - generalization: finite means are implicit → arbitrary probability laws on [0, ∞), means may be ∞; reason: the case of finite means is a special case of the Lean statement
-- source:
--   Feldman, Gkatzelis, Gravin & Schoepflin, Bayesian and Randomized Clock Auctions, arXiv:2202.09291v1, Section 3.2, p.11, "Note that E[…] is precisely the expected welfare"

import Mathlib
import Definitions.Def_BayesClock_IsDownwardClosed
import Definitions.Def_BayesClock_SinglePriceAuction
import Definitions.Def_BayesClock_uniformPriceValue

open MeasureTheory
open scoped NNReal ENNReal

namespace BayesClock

/-- The note of Feldman et al., arXiv:2202.09291v1, Section 3.2, p.11:
`E[max S ∈ 𝒮, ∑ i ∈ S, E[vᵢ | vᵢ ≥ p] · I[vᵢ ≥ p]]` "is precisely the expected welfare we get in a
single-price clock auction with a uniform price p".

**Formalization Note** The auction is existentially quantified: it posts `p` to every bidder, and its
rule `select` reads the set of acceptors only. An equality in `ℝ≥0∞`. -/
theorem uniform_price_welfare {N : Type*} [Fintype N] [DecidableEq N] (𝓕 : Finset (Finset N))
    (h𝓕 : IsDownwardClosed 𝓕) (ν : N → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (ν i)] (p : ℝ≥0) :
    ∃ a : SinglePriceAuction 𝓕, a.price = (fun _ => p) ∧
      a.expectedWelfare ν = uniformPriceValue 𝓕 ν p := by sorry

end BayesClock
