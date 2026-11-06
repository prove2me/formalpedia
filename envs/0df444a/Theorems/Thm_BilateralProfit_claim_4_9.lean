-- Prove2me | Theorems.Thm_BilateralProfit_claim_4_9
-- name    : BilateralProfit.claim_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:21:06.194614+00:00
-- url     : https://prove2.me/theorems/9bd07a81-3ae2-45b5-b2d9-fd70ad7cc25f
-- title:
--   Claim 4.9 — the telescoping prices are in $\mathcal A$, $2\varepsilon$-optimal, with monotone terms
-- statement:
--   Let $K\ge1$, $\rho$ a distribution on $G_K\times\mathcal A$, and $\varepsilon\in(0,1]$ the precision of Lemma 4.8. Let $(p,q)\in\mathcal A$ be $\varepsilon$-optimal according to $P_0$, i.e. $\Delta_\rho(a^\star,(p,q))\le\varepsilon$. Let $I_0\supseteq\dots\supseteq I_h=\{p\}$ be the root-to-leaf path of $p$ in the seller tree, and $D_j$ the buyer block of $I_j$ (Algorithm 3, built with $\nu$ and $\varepsilon$) containing $q$. Then:
--
--   1. every price $(p_{I_j,D_j},q)$ of the telescoping decomposition (21), with $p_{I_j,D_j}$ the representative (19), lies in $\mathcal A$ and satisfies $\Delta_\rho(a^\star,(p_{I_j,D_j},q))\le2\varepsilon$;
--   2. for the trade function $P$ of every valuation law on $[0,1]^2$, each parent-to-child term $q'\mapsto P(p_{I_j,D_j},q')-P(p_{I_{j-1},D_{j-1}},q')$ is monotone for $q'\in D_j\cap D_{j-1}$, and the root term $q'\mapsto P(p_{I_0,D_0},q')$ is monotone for $q'\in D_0$.
--
--   This makes the decomposition (21) a sum of monotone functions estimable by Claim 4.10 while querying only $2\varepsilon$-optimal prices.
--
--   **Formalization Note** Prices are grid indices; the tree, blocks and representatives are those of the `SellerTree` definitions. Monotone means non-decreasing or non-increasing.
--
--   Differences from the source:
--   - encoding: the setting of the proof of Lemma 4.8 (grid $G_K$, precision $\varepsilon\in(0,1]$) → hypotheses $0<K$, $0<\varepsilon\le1$; reason: the claim is stated inside that proof; $1/K$ needs $K\ge1$
--   - encoding: "contained in $\mathcal A$"; "monotone in $q$" → the representative's index is at most the buyer index; `MonotoneOn ∨ AntitoneOn` on the buyer indices of the block intersection; reason: a grid pair is in $\mathcal A$ iff its seller index is at most its buyer index
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Claim 4.9, p.26 (PDF 28); objects from Steps 1–4, pp.24–26 (PDF 26–28)

import Mathlib
import Definitions.Def_BilateralProfit_SellerTree

namespace BilateralProfit

open MeasureTheory

/-- **Claim 4.9**, Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), p.26
(PDF 28), in the proof of Lemma 4.8.

Fix `ρ` and the precision `ε ∈ (0, 1]`, and let `(p, q) ∈ 𝒜` be `ε`-optimal according to `P0`
(`Δ_ρ(a⋆, (p, q)) ≤ ε`). Along the root-to-leaf path `I_0 ⊇ ⋯ ⊇ I_h = {p}` of the seller tree,
with `D_j` the buyer block of `I_j` (Algorithm 3) containing `q`:
1. every price `(p_{I_j,D_j}, q)` of the telescoping decomposition (21) lies in `𝒜` and is
   `2ε`-optimal according to `P0`;
2. for every trade function `P` (of a valuation law on `[0,1]²`), each term
   `P(p_{I_j,D_j}, ·) − P(p_{I_{j−1},D_{j−1}}, ·)` is monotone on `D_j ∩ D_{j−1}`, and the root
   term `P(p_{I_0,D_0}, ·)` is monotone on `D_0`.

**Formalization Note.** Prices are grid indices (value index`/K`); the path, the blocks and the
representatives (19) are the definitions of `SellerTree`. "Monotone" is non-decreasing or
non-increasing. -/
theorem claim_4_9 (K : ℕ) (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (ε : ℝ)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (a : Act K) (ha : gapStar ρ a ≤ ε) :
    (∀ I ∈ sellerPath K a.1.1, repAt ρ ε I a.1.2 ≤ (a.1.2 : ℕ) ∧
      gapStarPt ρ ((repAt ρ ε I a.1.2 : ℝ) / K, ((a.1.2 : ℕ) : ℝ) / K) ≤ 2 * ε) ∧
    ∀ μ : Measure (ℝ × ℝ), IsValLaw μ →
      (∀ (m : ℕ) (hm : m + 1 < (sellerPath K a.1.1).length),
        MonotoneOn
            (fun q : ℕ => Ptrade μ ((repAt ρ ε ((sellerPath K a.1.1)[m + 1]'hm) a.1.2 : ℝ) / K,
                (q : ℝ) / K) -
              Ptrade μ ((repAt ρ ε ((sellerPath K a.1.1)[m]'(Nat.lt_of_succ_lt hm)) a.1.2 : ℝ) / K,
                (q : ℝ) / K))
            {q : ℕ | q ≤ K ∧
              blockStart ρ ε ((sellerPath K a.1.1)[m + 1]'hm).1
                ((sellerPath K a.1.1)[m + 1]'hm).2 q =
              blockStart ρ ε ((sellerPath K a.1.1)[m + 1]'hm).1
                ((sellerPath K a.1.1)[m + 1]'hm).2 a.1.2 ∧
              blockStart ρ ε ((sellerPath K a.1.1)[m]'(Nat.lt_of_succ_lt hm)).1
                ((sellerPath K a.1.1)[m]'(Nat.lt_of_succ_lt hm)).2 q =
              blockStart ρ ε ((sellerPath K a.1.1)[m]'(Nat.lt_of_succ_lt hm)).1
                ((sellerPath K a.1.1)[m]'(Nat.lt_of_succ_lt hm)).2 a.1.2} ∨
        AntitoneOn
            (fun q : ℕ => Ptrade μ ((repAt ρ ε ((sellerPath K a.1.1)[m + 1]'hm) a.1.2 : ℝ) / K,
                (q : ℝ) / K) -
              Ptrade μ ((repAt ρ ε ((sellerPath K a.1.1)[m]'(Nat.lt_of_succ_lt hm)) a.1.2 : ℝ) / K,
                (q : ℝ) / K))
            {q : ℕ | q ≤ K ∧
              blockStart ρ ε ((sellerPath K a.1.1)[m + 1]'hm).1
                ((sellerPath K a.1.1)[m + 1]'hm).2 q =
              blockStart ρ ε ((sellerPath K a.1.1)[m + 1]'hm).1
                ((sellerPath K a.1.1)[m + 1]'hm).2 a.1.2 ∧
              blockStart ρ ε ((sellerPath K a.1.1)[m]'(Nat.lt_of_succ_lt hm)).1
                ((sellerPath K a.1.1)[m]'(Nat.lt_of_succ_lt hm)).2 q =
              blockStart ρ ε ((sellerPath K a.1.1)[m]'(Nat.lt_of_succ_lt hm)).1
                ((sellerPath K a.1.1)[m]'(Nat.lt_of_succ_lt hm)).2 a.1.2}) ∧
      (MonotoneOn (fun q : ℕ => Ptrade μ ((repAt ρ ε (0, K + 1) a.1.2 : ℝ) / K, (q : ℝ) / K))
          {q : ℕ | q ≤ K ∧ blockStart ρ ε 0 (K + 1) q = blockStart ρ ε 0 (K + 1) a.1.2} ∨
        AntitoneOn (fun q : ℕ => Ptrade μ ((repAt ρ ε (0, K + 1) a.1.2 : ℝ) / K, (q : ℝ) / K))
          {q : ℕ | q ≤ K ∧ blockStart ρ ε 0 (K + 1) q = blockStart ρ ε 0 (K + 1) a.1.2}) := by sorry

end BilateralProfit
