-- Prove2me | Theorems.Thm_BlockchainTFM_lemma_1
-- name    : BlockchainTFM.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:03:29.713314+00:00
-- url     : https://prove2.me/theorems/97d0d535-61f8-4a53-af4d-0586114ce22a
-- title:
--   Lemma 1 (Myerson's Lemma): a TFM is U-DSIC iff its allocation is monotone and its payment satisfies (6)
-- statement:
--   Let $M=(\mathbf a,\mathbf p,r)$ be a transaction fee mechanism for $n$ users whose allocation $s\mapsto a_i(s,\mathbf b_{-i})$ is differentiable on $[0,1]$ for every user $i$ and every $\mathbf b_{-i}\in[0,1]^{n-1}$. Then $M$ is U-DSIC if and only if, for every $i$ and every $\mathbf b_{-i}$, the following two conditions hold.
--
--   1. **Monotone allocation:** $a_i(\cdot,\mathbf b_{-i})$ is non-decreasing on $[0,1]$.
--   2. **Constrained payment function:** for every $b_i\in[0,1]$,
--   $$a_i(b_i,\mathbf b_{-i})\,p_i(b_i,\mathbf b_{-i})=\int_0^{b_i}t\,\frac{\partial a_i(t,\mathbf b_{-i})}{\partial t}\,dt+a_i(0,\mathbf b_{-i})\,p_i(0,\mathbf b_{-i}).\qquad(6)$$
--
--   This is Myerson's characterization of dominant-strategy incentive compatibility, applied to the users' side of a TFM; the miner revenue rule plays no role. It shows that the dominant association (7) makes any monotone allocation U-DSIC, which is the starting point of the auxiliary mechanism method.
--
--   **Formalization Note** The derivative is taken within $[0,1]$ (one-sided at the end points) and is assumed interval integrable on $[0,1]$.
--
--   Differences from the source:
--   - generalization: a TFM has a : [0,1]ⁿ → [0,1]ⁿ (Definition 1) → any real-valued allocation rule; reason: the characterization does not use the range of a; every TFM of Definition 1 is an instance
--   - reading: ∂a_i(t,b_{−i})/∂t in (6), with no regularity stated → s ↦ a_i(s,b_{−i}) differentiable on [0,1] (one-sided at 0 and 1) with interval-integrable derivative, for every i and b_{−i} ∈ [0,1]^{n−1}; reason: the formula presupposes the derivative; Mechanism 3's allocation is smooth in the own bid
--   - encoding: users 1,…,n; b_{−i}; bids and values in [0,1] → Fin n; a vector b ∈ [0,1]ⁿ whose i-th entry is overwritten (Function.update); bids, values and deviations in Set.Icc 0 1; reason: Lean convention; same instances
-- source:
--   Chen, Simchi-Levi, Zhao, Zhou, Bayesian Mechanism Design for Blockchain Transaction Fee Allocation, arXiv:2209.13099v7, §4.1, Lemma 1 (6), p.21

import Mathlib
import Definitions.Def_BlockchainTFM_Model
import Definitions.Def_BlockchainTFM_Properties

open MeasureTheory

namespace BlockchainTFM

/-- **Lemma 1 (Myerson's Lemma)**, Chen–Simchi-Levi–Zhao–Zhou, arXiv:2209.13099v7, p.21.
Any TFM `M = (a, p, r)` is U-DSIC if and only if, for every user `i` and every `b_{-i}`,
* (monotone allocation) `a_i(·, b_{-i})` is non-decreasing on `[0,1]`, and
* (constrained payment function, (6)) for every `b_i ∈ [0,1]`,
  `a_i(b_i, b_{-i}) p_i(b_i, b_{-i}) = ∫₀^{b_i} t ∂a_i(t, b_{-i})/∂t dt + a_i(0, b_{-i}) p_i(0, b_{-i})`.

**Formalization Note.** (6) involves `∂a_i(t, b_{-i})/∂t`, so the lemma is read for allocation
rules with `s ↦ a_i(s, b_{-i})` differentiable on `[0,1]` (one-sided at the end points,
`derivWithin`) with interval-integrable derivative, for every `i` and `b_{-i} ∈ [0,1]^{n−1}`.
Bids, values and `b_{-i}` range over `[0,1]`. -/
theorem lemma_1 {n : ℕ} (M : TFM n)
    (hdiff : ∀ i : Fin n, ∀ b ∈ bidBox n,
      DifferentiableOn ℝ (fun s => M.alloc (Function.update b i s) i) (Set.Icc 0 1) ∧
        IntervalIntegrable
          (derivWithin (fun s => M.alloc (Function.update b i s) i) (Set.Icc 0 1)) volume 0 1) :
    IsUDSIC M ↔
      ∀ i : Fin n, ∀ b ∈ bidBox n,
        MonotoneOn (fun s => M.alloc (Function.update b i s) i) (Set.Icc 0 1) ∧
        ∀ x ∈ Set.Icc (0 : ℝ) 1,
          M.alloc (Function.update b i x) i * M.pay (Function.update b i x) i =
            (∫ t in (0 : ℝ)..x,
                t * derivWithin (fun s => M.alloc (Function.update b i s) i) (Set.Icc 0 1) t) +
              M.alloc (Function.update b i 0) i * M.pay (Function.update b i 0) i := by sorry

end BlockchainTFM
