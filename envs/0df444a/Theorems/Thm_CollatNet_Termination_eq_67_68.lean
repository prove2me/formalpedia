-- Prove2me | Theorems.Thm_CollatNet_Termination_eq_67_68
-- name    : CollatNet.Termination.eq_67_68
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:50:58.368061+00:00
-- url     : https://prove2.me/theorems/5d7ea923-54b9-41cf-9308-fc1d0aa6ef02
-- title:
--   (67)–(68), p. 45 (PDF 46) — L^s − L^f = Σ_{D^(1)}(Σ_{ℓ≥2} p^(ℓ)_i − q^(2)_i) − Σ_{D^f−D^(1)}(v_i − Σ_{ℓ≥2} p^(ℓ)_i)
-- statement:
--   Let the network satisfy the standing assumptions, with collateral price $1$, let $p^{(1)}, \dots, p^{(R)}$ be full-termination clearing payments, and let $q^{(2)}$ be selective-termination round-2 clearing payments (with $q^{(1)} = p^{(1)}$). Then the difference of the payment shortfalls is
--   $$
--   L^s - L^f = \sum_{i \in D^{(1)}} \Big(\sum_{\ell \ge 2} p^{(\ell)}_i - q^{(2)}_i\Big) - \sum_{i \in D^f - D^{(1)}} \Big(v_i - \sum_{\ell \ge 2} p^{(\ell)}_i\Big),
--   $$
--   where $p^{(\ell)}_i = \sum_j p^{(\ell)}_{ij}$, $q^{(2)}_i = \sum_j q^{(2)}_{ij}$, and the sums over $\ell$ run over rounds $2, \dots, R$.
--
--   This bookkeeping identity uses $D^{(1)} \subseteq D^f$ and the fact that a node outside $D^{(1)}$ meets its first-round obligations, $p^{(1)}_i = \bar p_i$; it reduces Proposition 5.2 to Lemma 5.1 and the net-worth bound.
-- source:
--   Ghamami, Glasserman & Young, Collateralized networks, accepted manuscript (Management Science 68(3), 2022; LSE Research Online 107496, version November 2020), proof of Proposition 5.2 (A.9), p. 45 (PDF 46), (67)–(68)

import Mathlib
import Definitions.Def_CollatNet_Termination_Model

namespace CollatNet.Termination

open Finset

/-- (67)–(68), p. 45: `L^s − L^f = Σ_{i ∈ D^(1)} (Σ_{ℓ ≥ 2} p^(ℓ)_i − q^(2)_i) −
Σ_{i ∈ D^f − D^(1)} (v_i − Σ_{ℓ ≥ 2} p^(ℓ)_i)`, for any selective-termination round-2 payments. -/
theorem eq_67_68 {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Network ι)
    (hX : X.Standing) (p : ℕ → ι → ι → ℝ) (hp : ClearsFT X p) (q2 : ι → ι → ℝ)
    (hq2 : q2 ∈ round2ST X (p 1)) :
    shortfallST X (p 1) q2 - shortfallFT X p =
      ∑ i ∈ D1 X (p 1), (∑ l ∈ Icc 2 (numRounds ι), ∑ j, p l i j - ∑ j, q2 i j) -
        ∑ i ∈ Df X p \ D1 X (p 1),
          (vTot X i - ∑ l ∈ Icc 2 (numRounds ι), ∑ j, p l i j) := by sorry

end CollatNet.Termination
