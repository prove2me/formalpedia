-- Prove2me | Theorems.Thm_BlockchainTFM_lemma_EC_3
-- name    : BlockchainTFM.lemma_EC_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:03:44.487232+00:00
-- url     : https://prove2.me/theorems/9d67b487-b0d8-40c8-b2b8-0fe380c83766
-- title:
--   Lemma EC.3: a TFM is 1-SCP iff its allocation is monotone and $a_ip_i-r$ satisfies (EC.36)
-- statement:
--   Let $M=(\mathbf a,\mathbf p,r)$ be a transaction fee mechanism for $n$ users whose allocation $s\mapsto a_i(s,\mathbf b_{-i})$ is differentiable on $[0,1]$ for every user $i$ and every $\mathbf b_{-i}\in[0,1]^{n-1}$. Then $M$ is 1-SCP if and only if, for every $i$ and every $\mathbf b_{-i}$:
--
--   1. **Monotone allocation:** $a_i(\cdot,\mathbf b_{-i})$ is non-decreasing on $[0,1]$;
--   2. **Constrained payment function:** for every $b_i\in[0,1]$,
--   $$a_i(b_i,\mathbf b_{-i})p_i(b_i,\mathbf b_{-i})-r(b_i,\mathbf b_{-i})=\int_0^{b_i}t\,\frac{\partial a_i(t,\mathbf b_{-i})}{\partial t}\,dt+a_i(0,\mathbf b_{-i})p_i(0,\mathbf b_{-i})-r(0,\mathbf b_{-i}).\qquad(\text{EC.36})$$
--
--   Here 1-SCP means that the miner together with one user $i$ cannot strictly increase their total utility $u_i+r$ by changing user $i$'s bid, whatever the other bids. The lemma is the collusion-proof analogue of Myerson's Lemma and is the step that turns admissibility condition (10) into 1-SCP in the proof of Theorem 2.
--
--   **Formalization Note** As in Lemma 1, the derivative is taken within $[0,1]$ and assumed interval integrable.
--
--   Differences from the source:
--   - generalization: a TFM has a : [0,1]ⁿ → [0,1]ⁿ (Definition 1) → any real-valued allocation rule; reason: the characterization does not use the range of a; every TFM of Definition 1 is an instance
--   - reading: ∂a_i(t,b_{−i})/∂t in (6), with no regularity stated → s ↦ a_i(s,b_{−i}) differentiable on [0,1] (one-sided at 0 and 1) with interval-integrable derivative, for every i and b_{−i} ∈ [0,1]^{n−1}; reason: the formula presupposes the derivative; Mechanism 3's allocation is smooth in the own bid
--   - reading: c-SCP with c = 1 (Definition 6): the miner colludes with at most one user → the miner and user i cannot raise u_i + r by changing user i's bid, for every b_{−i}, value v and deviation x in [0,1] (IsOneSCP); reason: the paper's deviation MU₁-UB; the other users bid truthfully (their equilibrium under U-BNIC) and the miner knows all bids, so the condition is ex post
--   - encoding: users 1,…,n; b_{−i}; bids and values in [0,1] → Fin n; a vector b ∈ [0,1]ⁿ whose i-th entry is overwritten (Function.update); bids, values and deviations in Set.Icc 0 1; reason: Lean convention; same instances
-- source:
--   Chen, Simchi-Levi, Zhao, Zhou, Bayesian Mechanism Design for Blockchain Transaction Fee Allocation, arXiv:2209.13099v7, Appendix EC.4.1, Lemma EC.3 (EC.36), pp.ec10–ec11

import Mathlib
import Definitions.Def_BlockchainTFM_Model
import Definitions.Def_BlockchainTFM_Properties

open MeasureTheory

namespace BlockchainTFM

/-- **Lemma EC.3**, Chen–Simchi-Levi–Zhao–Zhou, arXiv:2209.13099v7, pp.ec10–ec11. The mechanism
`M = (a, p, r)` is 1-SCP if and only if, for every user `i` and every `b_{-i}`,
* (monotone allocation) `a_i(·, b_{-i})` is non-decreasing on `[0,1]`, and
* (constrained payment function, (EC.36)) for every `b_i ∈ [0,1]`,
  `a_i(b_i, b_{-i}) p_i(b_i, b_{-i}) − r(b_i, b_{-i})
    = ∫₀^{b_i} t ∂a_i(t, b_{-i})/∂t dt + a_i(0, b_{-i}) p_i(0, b_{-i}) − r(0, b_{-i})`.

**Formalization Note.** As for Lemma 1, the lemma is read for allocation rules with
`s ↦ a_i(s, b_{-i})` differentiable on `[0,1]` (`derivWithin`, one-sided at the end points) with
interval-integrable derivative. 1-SCP is `IsOneSCP` (the miner and one user cannot raise
`u_i + r` by changing user `i`'s bid). -/
theorem lemma_EC_3 {n : ℕ} (M : TFM n)
    (hdiff : ∀ i : Fin n, ∀ b ∈ bidBox n,
      DifferentiableOn ℝ (fun s => M.alloc (Function.update b i s) i) (Set.Icc 0 1) ∧
        IntervalIntegrable
          (derivWithin (fun s => M.alloc (Function.update b i s) i) (Set.Icc 0 1)) volume 0 1) :
    IsOneSCP M ↔
      ∀ i : Fin n, ∀ b ∈ bidBox n,
        MonotoneOn (fun s => M.alloc (Function.update b i s) i) (Set.Icc 0 1) ∧
        ∀ x ∈ Set.Icc (0 : ℝ) 1,
          M.alloc (Function.update b i x) i * M.pay (Function.update b i x) i -
              M.rev (Function.update b i x) =
            (∫ t in (0 : ℝ)..x,
                t * derivWithin (fun s => M.alloc (Function.update b i s) i) (Set.Icc 0 1) t) +
              M.alloc (Function.update b i 0) i * M.pay (Function.update b i 0) i -
              M.rev (Function.update b i 0) := by sorry

end BlockchainTFM
