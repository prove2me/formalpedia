-- Prove2me | Theorems.Thm_AnyPriceShare_Bidding_lemma_4_4
-- name    : AnyPriceShare.Bidding.lemma_4_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:56.365493+00:00
-- url     : https://prove2.me/theorems/851bf685-e95b-4d29-80a6-00a9ed8b2b7a
-- title:
--   Lemma 4.4, p. 15 — bid-your-max-value secures k/(k+1) of the proportional share when no k items exceed it
-- statement:
--   Consider the Bidding Game with $n$ agents whose budgets are their entitlements $b_1,\dots,b_n$ ($b_k>0$, $\sum_kb_k=1$), and an agent $i$ with additive non-negative item values $v(j)$; write $v(M)$ for the value of all items. Let $k$ be a positive integer such that no set of at most $k$ items has value larger than the proportional share:
--   $$v(T)\le b_i\cdot v(M)\quad\text{for every set } T \text{ of at most } k \text{ items}.$$
--   Then every bid-your-max-value strategy of agent $i$ guarantees her, regardless of the strategies of the other agents, a bundle of value at least
--   $$\frac{k}{k+1}\cdot b_i\cdot v(M).$$
--
--   The lemma is the paper's basic tool for instances in which every single item is small compared with the proportional share.
--
--   **Formalization Note** The paper's "no subset of $k$ items" is read as "no set of at most $k$ items". For $m\ge k$ the two readings agree because values are non-negative; for $m<k$ the literal reading would be vacuous and the lemma false (one item of value $1$, $b_i=1/3$, $k=2$: agent $i$ bids $1/3$ and another agent with budget $2/3$ outbids her, leaving her $0<2/9$). The paper's proof uses the "at most $k$" form. The lemma is stated for every strategy satisfying the bid-your-max-value rule, so every tie-break between equally valuable items is covered.
-- source:
--   Babaioff, Ezra & Feige, Fair-Share Allocations for Agents with Arbitrary Entitlements, arXiv:2103.04304v4, p. 15, Lemma 4.4 (strategy defined on p. 15; proof pp. 15–16)

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_AnyPriceShare_Bidding_Game

namespace AnyPriceShare.Bidding

/-- Lemma 4.4, p. 15: in the Bidding Game with entitlements `b` (`b k > 0`, `∑ b k = 1`), if for a
positive integer `k` no set of at most `k` items has value larger than the proportional share
`b_i · v(M)`, then every bid-your-max-value strategy of agent `i` guarantees her at least
`k/(k+1) · b_i · v(M)`, regardless of the strategies of the other agents. -/
theorem lemma_4_4 {n m : ℕ} (v : Fin m → ℝ) (hv : ∀ j, 0 ≤ v j)
    (b : Fin n → ℝ) (hb : ∀ k, 0 < b k) (hsum : ∑ k, b k = 1) (i : Fin n)
    (k : ℕ) (hk : 0 < k)
    (hsmall : ∀ T : Finset (Fin m), T.card ≤ k → addVal v T ≤ b i * addVal v Finset.univ)
    (σ : Strategy n m) (hσ : IsBidYourMaxValue v b i σ) :
    Guarantees b σ i v ((k : ℝ) / (k + 1) * b i * addVal v Finset.univ) := by sorry

end AnyPriceShare.Bidding
