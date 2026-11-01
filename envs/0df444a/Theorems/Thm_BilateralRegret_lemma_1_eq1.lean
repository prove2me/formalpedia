-- Prove2me | Theorems.Thm_BilateralRegret_lemma_1_eq1
-- name    : BilateralRegret.lemma_1_eq1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:12:26.267364+00:00
-- url     : https://prove2.me/theorems/f628fdd5-38e7-48c6-8e17-63d325fd7d26
-- title:
--   Lemma 1, eq. (1) — pointwise decomposition of the gain from trade
-- statement:
--   Fix a price $p\in[0,1]$. For all valuations $s,b\in[0,1]$,
--
--   $$
--   \mathrm{GFT}(p,s,b)=\int_{[p,1]}\mathbb I[s\le p\le\lambda\le b]\,d\lambda+\int_{[0,p]}\mathbb I[s\le\lambda\le p\le b]\,d\lambda .
--   $$
--
--   The surplus $b-s$ of a trade at $p$ is split into the part above the price and the part below it. Taking expectations gives the Decomposition lemma, which separates the expected gain from trade into terms that depend on yes/no answers only.
--
--   Differences from the source:
--   - encoding: ∫_{[p,1]} … dλ and ∫_{[0,p]} … dλ → Lebesgue set integrals over Icc p 1 and Icc 0 p of the real indicator ind; reason: standard Lean notation; same values
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Fusco, Leonardi, Bilateral Trade: A Regret Minimization Perspective, arXiv:2109.12974v1, Lemma 1, eq. (1), p.7 (proof p.21)

import Mathlib
import Definitions.Def_BilateralRegret_GFT

namespace BilateralRegret

open MeasureTheory

/-- **Lemma 1, eq. (1) (Decomposition lemma, pointwise form).**
Cesa-Bianchi, Cesari, Colomboni, Fusco, Leonardi, *Bilateral Trade: A Regret Minimization
Perspective*, arXiv:2109.12974v1, §3, p.7.

For every price `p ∈ [0,1]` and all `s, b ∈ [0,1]`,
`GFT(p, s, b) = ∫_{[p,1]} 𝕀[s ≤ p ≤ λ ≤ b] dλ + ∫_{[0,p]} 𝕀[s ≤ λ ≤ p ≤ b] dλ`.

**Formalization Note.** The integrals are Lebesgue set integrals over `Icc p 1` and `Icc 0 p`. -/
theorem lemma_1_eq1 (p s b : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    GFT p s b = (∫ l in Set.Icc p 1, ind (s ≤ p ∧ p ≤ l ∧ l ≤ b))
      + ∫ l in Set.Icc 0 p, ind (s ≤ l ∧ l ≤ p ∧ p ≤ b) := by sorry

end BilateralRegret
