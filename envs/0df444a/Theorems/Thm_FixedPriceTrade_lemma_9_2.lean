-- Prove2me | Theorems.Thm_FixedPriceTrade_lemma_9_2
-- name    : FixedPriceTrade.lemma_9_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:41:45.647907+00:00
-- url     : https://prove2.me/theorems/c74cc3f6-0d19-4d57-ab8e-99ec3f9aa448
-- title:
--   Lemma 9.2 — bounded hard pairs and the identities (43)–(44)
-- statement:
--   Let $H:[0,1]\to[0,1]$ be continuous and nonincreasing with $H(1)=\eta>0$, and let $d>0$. The hard pair of $(d,H)$ (buyer survival function $H$ on $[0,1]$, $\eta$ on $[1,R_\eta)$, $0$ from $R_\eta=1+d/\eta$ on; seller CDF $F_s=d(L^{-1}-HT)$ on $[0,1)$ completed by an atom at one) exists, so $F_s$ is a valid seller CDF. With $T_\eta=T(1)$ and $J_\eta=J_d(H(1-\cdot))$, the pair satisfies
--   $$
--   M_\eta=1-d^2T_\eta,\qquad \Gamma_{\max,\eta}=d+\eta d^2T_\eta,\qquad G_\eta=d+d\cdot J_\eta-d^3T_\eta .
--   $$
--   In particular, for every $\beta$,
--   $$
--   \Gamma_{\max,\eta}-\beta G_\eta+\beta d\cdot M_\eta=d(1-\beta J_\eta)+\eta d^2T_\eta .
--   $$
--   These pairs make Lemma 9.1 tight up to the residual $\eta d^2T_\eta$.
--
--   Differences from the source:
--   - encoding: independent values V_s, V_b → the joint law is the product μs.prod μb of the two laws; reason: for independent variables the joint law is the product, and every quantity used depends only on the joint law
--   - encoding: extend H to a buyer survival function; F_s completed by an atom at one; 'this is a valid seller CDF' → the predicate IsHardPair d H, which pins both laws, and the clause that such a pair exists; reason: a law on ℝ is determined by its CDF; existence is the validity claim
--   - encoding: Γ_max,η → gammaMax, the supremum of Γ over z ≥ 0; reason: the mission-wide definition of Γ_max
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 26832346…), Lemma 9.2, pp.21–22

import Mathlib
import Definitions.Def_FixedPriceTrade_welfareRatio
import Definitions.Def_FixedPriceTrade_J
import Definitions.Def_FixedPriceTrade_IsHardPair

set_option autoImplicit false

namespace FixedPriceTrade

open MeasureTheory Set

/-- **Lemma 9.2 (bounded hard pairs)** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact Welfare
Guarantee of Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…),
pp.21–22.

Let `H : [0,1] → [0,1]` be continuous and nonincreasing with `H(1) = η > 0`, and let `d > 0`.
The buyer law with survival function `H` on `[0,1]`, `η` on `[1, R_η)`, `0` at and above
`R_η = 1 + d/η` (atom `1 − H(0)` at zero), and the seller law with CDF
`F_s = d(L^{−1} − H T)` on `[0, 1)` completed by an atom at one, exist (a valid pair), and with
`T_η = T(1)`, `J_η = J_d(H(1 − ·))`:
`M_η = 1 − d² T_η`, `Γ_max,η = d + η d² T_η`, `G_η = d + d J_η − d³ T_η` (43), and for every `β`,
`Γ_max,η − β G_η + β d M_η = d(1 − β J_η) + η d² T_η` (44).

**Formalization Note.** The pair is `IsHardPair d H`, which determines both laws. `η = 1`
(`H ≡ 1` allowed) is included. -/
theorem lemma_9_2 (d : ℝ) (hd : 0 < d) (H : ℝ → ℝ) (η : ℝ)
    (hcont : ContinuousOn H (Icc 0 1)) (hanti : AntitoneOn H (Icc 0 1))
    (hrange : ∀ s ∈ Icc (0 : ℝ) 1, H s ∈ Icc (0 : ℝ) 1) (hH1 : H 1 = η) (hη : 0 < η) :
    (∃ μs μb : Measure ℝ, IsHardPair d H μs μb) ∧
    ∀ μs μb : Measure ℝ, IsHardPair d H μs μb →
      sellerMean μs = 1 - d ^ 2 * hardT d H 1 ∧
      gammaMax μs μb = d + η * d ^ 2 * hardT d H 1 ∧
      firstBestGFT μs μb = d + d * J d (fun t => H (1 - t)) - d ^ 3 * hardT d H 1 ∧
      ∀ β : ℝ, gammaMax μs μb - β * firstBestGFT μs μb + β * d * sellerMean μs =
        d * (1 - β * J d (fun t => H (1 - t))) + η * d ^ 2 * hardT d H 1 := by sorry

end FixedPriceTrade
