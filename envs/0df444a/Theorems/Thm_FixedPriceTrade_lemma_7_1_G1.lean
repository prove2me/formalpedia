-- Prove2me | Theorems.Thm_FixedPriceTrade_lemma_7_1_G1
-- name    : FixedPriceTrade.lemma_7_1_G1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:43:44.904168+00:00
-- url     : https://prove2.me/theorems/b6f039ef-0510-4eaf-869c-f65bb960b08b
-- title:
--   Lemma 7.1, (G1) — the fixed-endpoint gap is a nonnegative integral
-- statement:
--   Let $d>0$, $h$ a measurable control with reciprocal state $p$ and endpoint $x$, and $P_x$ the reference curve with that endpoint (with $P\equiv1/d$ when $x=1/d$). With $v=\log(p/P_x)$,
--   $$
--   \Phi_d(x)-\mathcal F_d[p]=\int_0^\infty\Big[a(v')^2+\frac{e^{-2v}-1+2v}{P_x^2}-2Q_xv\Big]da\ \ge0,
--   $$
--   and the gap vanishes exactly when $p=P_x$.
--
--   At a fixed endpoint the energy is concave, and this identity certifies the reference curve as its maximizer.
--
--   Differences from the source:
--   - encoding: measurable h : [0,1] → [0,1] → measurable h : ℝ → ℝ with h(t) ∈ [0,1] for t ∈ [0,1]; reason: values outside [0,1] never enter a formula
--   - encoding: the reference curve P_x indexed by its endpoint x → refCurve d C indexed by the curvature parameter C, with endpoint x(C); C = 0 is the limiting endpoint x = 1/d, P ≡ 1/d (p.16); reason: Lemma 6.1 makes C ↦ x(C) a bijection of (0, C̄(d)) onto (0, 1/d), and p.16 sets the endpoint x = 1/d at C = 0
--   - encoding: the reference curve at p's endpoint → a C in {0} ∪ (0, C̄(d)) with x(C) = x exists, and the identity holds for every such C; reason: names the reference curve of the endpoint; existence is stated so the identity is not vacuous
--   - encoding: the integral of (G1) and of Φ_d(x) = F_d[P_x] → the integral of (G1) and of Φ_d(x) = F_d[P_x], with its integrand stated integrable on (0, ∞); reason: the paper's integrands are bounded with compact support; the conjunct rules out a Bochner 0 for a non-integrable function, and adds no assumption
--   - encoding: p = P_x → p(a) = P_x(a) for all a ≥ 0; reason: both are functions on [0, ∞)
--   - encoding: derivatives of absolutely continuous functions (p′, (log p)′, v′) → Mathlib's deriv; reason: deriv agrees almost everywhere with the derivative of an absolutely continuous function, and the derivatives appear only under integrals or a.e. statements
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 26832346…), Lemma 7.1, (G1), p.16

import Mathlib
import Definitions.Def_FixedPriceTrade_refCurve

set_option autoImplicit false

namespace FixedPriceTrade

open MeasureTheory Set

/-- **Lemma 7.1 (nonnegative gaps), (G1)** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact Welfare
Guarantee of Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…), p.16.

Let `d > 0`, `h` a control, `p` its reciprocal state (16) with endpoint `x = p(0)`, and `P_x` the
reference curve at that endpoint: `C ∈ (0, C̄(d))` with `x(C) = x`, or `C = 0` (`P ≡ 1/d`) when
`x = 1/d`. Such a `C` exists, and for every such `C`, with `v = log(p/P_x)`,
`Φ_d(x) − F_d[p] = ∫_0^∞ [a(v′)² + (e^{−2v} − 1 + 2v)/P_x² − 2Q_x v] da ≥ 0`, and it vanishes
exactly when `p = P_x` on `[0, ∞)`. The integrands of (G1) and of `Φ_d(x) = F_d[P_x]` are
integrable on `(0, ∞)`.

**Formalization Note.** The reference curve is indexed by `C` (`refCurve d C`, endpoint
`x(C)`); `C = 0` is the paper's limiting endpoint (p.16). `v′` is Mathlib's `deriv`. -/
theorem lemma_7_1_G1 (d : ℝ) (hd : 0 < d) (h : ℝ → ℝ) (hh : IsControl h) :
    (∃ C, (C = 0 ∨ C ∈ Ioo 0 (Cbar d)) ∧ endpointX d C = recipX d h) ∧
    ∀ C, (C = 0 ∨ C ∈ Ioo 0 (Cbar d)) → endpointX d C = recipX d h →
      IntegrableOn (fun a => d ^ 2 - 1 / refCurve d C a ^ 2 -
        a * deriv (fun b => Real.log (refCurve d C b)) a ^ 2) (Ioi 0) ∧
      IntegrableOn (gapIntegrand d h C) (Ioi 0) ∧
      Phi d C - energy d (recipP d h) = ∫ a in Ioi (0 : ℝ), gapIntegrand d h C a ∧
      0 ≤ ∫ a in Ioi (0 : ℝ), gapIntegrand d h C a ∧
      ((∫ a in Ioi (0 : ℝ), gapIntegrand d h C a) = 0 ↔
        ∀ a, 0 ≤ a → recipP d h a = refCurve d C a) := by sorry

end FixedPriceTrade
