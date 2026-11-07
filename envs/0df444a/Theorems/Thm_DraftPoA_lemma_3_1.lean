-- Prove2me | Theorems.Thm_DraftPoA_lemma_3_1
-- name    : DraftPoA.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:29.249047+00:00
-- url     : https://prove2.me/theorems/126105d5-b0fd-4ad9-ad42-9eac6d95016c
-- title:
--   Lemma 3.1 (Activation lemma): $u_i(d,b_{-i})\ge v_i(U)-p|U|-P_i(b)$
-- statement:
--   Fix a bidder $i$ whose valuation $v_i$ is normalized and monotone, a pure strategy profile $b=(b_i,b_{-i})$ on the grid $(\delta,\bar M)$ with $\delta\ge0$, and a grid price $p>0$. There is a pure strategy $d$, whose action at every node is that of the activation deviation $d(b_i,v_i,p)$ and therefore depends only on $b_i$, $v_i$ and $p$, such that for every set $U\subseteq M$ with $\pi^i_j(b)<p$ for all $j\in U$,
--
--   $$u_i(d,b_{-i})\ \ge\ v_i(U)-p|U|-P_i(b).$$
--
--   In particular $u_i(d,b_{-i})\ge\Phi_i(p;b)-P_i(b)$, where $\Phi_i$ is taken over the subsets of any set $O$ (the paper's $O=O_i$, her optimal bundle).
--
--   Until the deviation activates, the play follows the path of $b$, because a raised bid that loses is not announced; the lemma turns this into a guarantee at one price, which the covering lemma then spreads over a ladder of prices.
--
--   Differences from the source:
--   - generalization: In particular u_i(d, b_−i) ≥ Φ_i(p; b) − P_i(b), Φ_i over U ⊆ O_i → the same for every set O in place of O_i; reason: every eligible U ⊆ O satisfies the first claim; O = O_i is the source's case
--   - encoding: d = d(b_i, v_i, p), depending only on b_i, v_i and p → ∃ d : Strategy with d.act = activationAct i (b i).act (v i) p; reason: the action map is a function of b_i, v_i, p (and of i, whose holdings it reads); legality is part of the existence claim
--   - encoding: ties among nonempty maximizing demand sets broken by a fixed rule → a fixed choice function; reason: any fixed rule is allowed by the source
-- source:
--   Truong, Thach, Chan, Guo, The Price of Anarchy of Draft Auctions, STOC 2027 submission (manuscript sha256 270ffdaa…), Lemma 3.1, p.6 (PDF 7); proof App. A.1, pp.15–16 (PDF 16–17)

import Mathlib
import Definitions.Def_ComplementFreeCA_CFRounding_Auction
import Definitions.Def_DraftPoA_Auction
import Definitions.Def_DraftPoA_Activation

open ComplementFreeCA.CFRounding

namespace DraftPoA

/-- Lemma 3.1 (Activation lemma), p.6 (PDF 7); proof App. A.1, pp.15–16 (Truong, Thach, Chan, Guo, *The Price of Anarchy of Draft Auctions*, STOC 2027 submission (manuscript sha256 270ffdaa…)).

Fix a bidder `i` with a normalized monotone valuation, a pure profile `b` on the grid `(δ, M̄)`
and a grid price `p > 0`. There is a pure strategy `d` whose action map is the activation
deviation `d(b_i, v_i, p)` (it reads only `b_i`, `v_i` and `p`) such that for every set `U` of
items with `π^i_j(b) < p` for all `j ∈ U`,
`u_i(d, b_{−i}) ≥ v_i(U) − p|U| − P_i(b)`; in particular `u_i(d, b_{−i}) ≥ Φ_i(p; b) − P_i(b)`.

**Formalization Note.** "Depending only on `b_i`, `v_i` and `p`" is the equation
`d.act = activationAct i (b i).act (v i) p`. The "in particular" is stated for every set `O` in
the role of the optimal bundle `O_i` (a generalization: the paper takes `O = O_i`). `U` ranges
over all sets of items, as printed. -/
theorem lemma_3_1 {n m : ℕ} [NeZero n] {δ Mbar : ℝ} (hδ : 0 ≤ δ) (prio : Equiv.Perm (Fin n))
    (v : Fin n → Finset (Fin m) → ℝ) (b : Fin n → Strategy n m δ Mbar) (i : Fin n)
    (hvi : IsNormalized (v i) ∧ IsMonotone (v i)) (p : ℝ) (hp : IsGridBid δ Mbar p)
    (hp0 : 0 < p) :
    ∃ d : Strategy n m δ Mbar, d.act = activationAct i (b i).act (v i) p ∧
      (∀ U : Finset (Fin m), (∀ j ∈ U, compPrice prio b i j < p) →
        v i U - p * (U.card : ℝ) - payment (play prio b) i ≤
          u prio v (Function.update b i d) i) ∧
      (∀ O : Finset (Fin m),
        singlePriceProfit (v i) O (compPrice prio b i) p - payment (play prio b) i ≤
          u prio v (Function.update b i d) i) := by sorry

end DraftPoA
