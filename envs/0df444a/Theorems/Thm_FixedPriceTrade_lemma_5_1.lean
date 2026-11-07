-- Prove2me | Theorems.Thm_FixedPriceTrade_lemma_5_1
-- name    : FixedPriceTrade.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:42:21.68777+00:00
-- url     : https://prove2.me/theorems/9b25911e-2406-4bdb-90b9-29ea548a5fe4
-- title:
--   Lemma 5.1 — energy representation $J_d(h)-1=\mathcal F_d[p]$
-- statement:
--   Let $d>0$ and let $h:[0,1]\to[0,1]$ be measurable, with reciprocal clock $A$, reciprocal state $p$ and endpoint $x=p(0)$ from (16). Then $p$ is absolutely continuous, and
--   $$
--   p'(A(t))=h(t)\ \text{for a.e. }t\in[0,1],\qquad p(a)\le\min\{x+a,1/d\}\ (a\ge0),\qquad \frac1{d+1}\le x\le\frac1d,
--   $$
--   and
--   $$
--   J_d(h)-1=\mathcal F_d[p]=-\log(d\cdot x)+\int_0^\infty\Big[d^2-p^{-2}-a\big((\log p)'\big)^2\Big]da .
--   $$
--   The reciprocal clock collects the memory of the second-moment term into the weight $a$, turning $J_d$ into a local energy with two upper obstacles.
--
--   Differences from the source:
--   - encoding: measurable h : [0,1] → [0,1] → measurable h : ℝ → ℝ with h(t) ∈ [0,1] for t ∈ [0,1]; reason: values outside [0,1] never enter a formula
--   - encoding: p absolutely continuous → AbsolutelyContinuousOnInterval p 0 b for every b ≥ 0; reason: p is a function on [0, ∞); absolute continuity there means on every compact interval
--   - encoding: x = p(0) (definition in (16)) → the clause p(0) = x; reason: p and x are separate definitions in Lean; the clause records (16)
--   - encoding: derivatives of absolutely continuous functions (p′, (log p)′, v′) → Mathlib's deriv; reason: deriv agrees almost everywhere with the derivative of an absolutely continuous function, and the derivatives appear only under integrals or a.e. statements
--   - encoding: the integral in (E) → the integral in (E), with its integrand stated integrable on (0, ∞); reason: the paper's integrands are bounded with compact support; the conjunct rules out a Bochner 0 for a non-integrable function, and adds no assumption
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 26832346…), Lemma 5.1, p.13

import Mathlib
import Definitions.Def_FixedPriceTrade_energy

set_option autoImplicit false

namespace FixedPriceTrade

open MeasureTheory Set

/-- **Lemma 5.1 (energy representation)** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact Welfare
Guarantee of Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…), p.13.

For every `d > 0`, a measurable `h : [0,1] → [0,1]` induces through (16) an absolutely continuous
`p` (on every `[0, b]`) with `p(0) = x`, `p′(A(t)) = h(t)` for almost every `t ∈ [0,1]`,
`p(a) ≤ min{x + a, 1/d}` for `a ≥ 0`, `1/(d + 1) ≤ x ≤ 1/d`, and
`J_d(h) − 1 = F_d[p] = −log(d·x) + ∫_0^∞ [d² − p^{−2} − a((log p)′)²] da`, the integrand being
integrable on `(0, ∞)`.

**Formalization Note.** The derivative of `p` is Mathlib's `deriv`; "a.e." is in `t` for Lebesgue
measure on `[0,1]`. The integrability conjunct guards against a Bochner `0`. -/
theorem lemma_5_1 (d : ℝ) (hd : 0 < d) (h : ℝ → ℝ) (hh : IsControl h) :
    (∀ b, 0 ≤ b → AbsolutelyContinuousOnInterval (recipP d h) 0 b) ∧
    recipP d h 0 = recipX d h ∧
    (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), deriv (recipP d h) (Aclock d h t) = h t) ∧
    (∀ a, 0 ≤ a → recipP d h a ≤ min (recipX d h + a) (1 / d)) ∧
    1 / (d + 1) ≤ recipX d h ∧ recipX d h ≤ 1 / d ∧
    IntegrableOn (fun a => d ^ 2 - 1 / recipP d h a ^ 2 -
      a * deriv (fun b => Real.log (recipP d h b)) a ^ 2) (Ioi 0) ∧
    J d h - 1 = energy d (recipP d h) := by sorry

end FixedPriceTrade
