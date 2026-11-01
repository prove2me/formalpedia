-- Prove2me | Theorems.Thm_BlockchainTFM_proposition_EC_1
-- name    : BlockchainTFM.proposition_EC_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:03:39.001592+00:00
-- url     : https://prove2.me/theorems/8863ed56-3149-4a66-b720-3d5626e850df
-- title:
--   Proposition EC.1: a fake bid does not raise a truthful user's utility in the auxiliary mechanism for block size $k$
-- statement:
--   For any user $i$, adding a fake bid will not benefit her utility in the auxiliary mechanism $M$ for block size $k$.
--
--   Precisely: let $k\ge1$, $m\ge0$ and let $M=(\mathbf a,\mathbf p,0)$ be the auxiliary mechanism of Mechanism 3 (allocation by $k$-round weighted sampling without replacement with weights $e^{mb_j}$, payment the dominant association). Let $\mathbf b\in[0,1]^n$ be a bid vector in which user $i$ bids her valuation $b_i$. For every fake bid $x\in[0,1]$ appended as an $(n+1)$-st bid,
--   $$u_i\bigl(b_i,(\mathbf b_{-i},x);\,b_i\bigr)\ \le\ u_i\bigl(b_i,\mathbf b_{-i};\,b_i\bigr),$$
--   the left side computed in the auxiliary mechanism with $n+1$ bids.
--
--   By (EC.138), a truthful user's utility in the auxiliary mechanism is $\int_0^{b_i}a_i(t,\mathbf b_{-i})\,dt$, so the proposition follows from Lemma EC.4. It is the auxiliary-mechanism part of the U-SP clause of Theorem 4.
--
--   **Formalization Note** "Her utility" is user $i$'s own utility; the fake identity's utility is not included (the U-SP argument treats it separately). The auxiliary payment is written in the form (EC.137).
--
--   Differences from the source:
--   - reading: 'her utility', adding a fake bid → user i's own utility u_i(b_i, ·; b_i) when bidding her valuation, with one fake bid x ∈ [0,1] appended last; reason: (EC.138) is the truthful utility the paper compares; the fake identity's utility is handled in EC.4.4.3
--   - encoding: users 1,…,n; b_{−i}; bids and values in [0,1] → Fin n; a vector b ∈ [0,1]ⁿ whose i-th entry is overwritten (Function.update); bids, values and deviations in Set.Icc 0 1; reason: Lean convention; same instances
-- source:
--   Chen, Simchi-Levi, Zhao, Zhou, Bayesian Mechanism Design for Blockchain Transaction Fee Allocation, arXiv:2209.13099v7, Appendix EC.4.4.3, Proposition EC.1 and (EC.137)–(EC.138), p.ec24

import Mathlib
import Definitions.Def_BlockchainTFM_Model
import Definitions.Def_BlockchainTFM_Mechanism3

namespace BlockchainTFM

/-- **Proposition EC.1**, Chen–Simchi-Levi–Zhao–Zhou, arXiv:2209.13099v7, p.ec24. For any user
`i`, adding a fake bid will not benefit her utility in the auxiliary mechanism `M` for block
size `k`.

For every block size `k ≥ 1`, logit parameter `m ≥ 0`, bid vector `b ∈ [0,1]ⁿ` in which user
`i` bids her valuation `b_i`, and every fake bid `x ∈ [0,1]` appended as an `(n+1)`-st bid,
user `i`'s utility `u_i(b_i, b_{-i}; b_i)` in the auxiliary mechanism with `n + 1` bids is at
most her utility with the original `n` bids.

**Formalization Note.** The auxiliary mechanism is `auxMech` (allocation of Mechanism 3, payment
the dominant association in the form (EC.137), miner revenue `0`). "Her utility" is user `i`'s
own utility; the fake identity's utility is not included (the paper's (C, N)-U-SP argument
treats it separately, EC.4.4.3). The fake bid is appended last (`Fin.snoc`), and user `i` is
`Fin.castSucc i` among `n + 1` bids. -/
theorem proposition_EC_1 {n : ℕ} (k : ℕ) (hk : 1 ≤ k) (m : ℝ) (hm : 0 ≤ m)
    (b : Fin n → ℝ) (hb : b ∈ bidBox n) (i : Fin n) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    utility (auxMech (n + 1) k m) (Fin.castSucc i) (Fin.snoc (α := fun _ => ℝ) b x) (b i) ≤
      utility (auxMech n k m) i b (b i) := by sorry

end BlockchainTFM
