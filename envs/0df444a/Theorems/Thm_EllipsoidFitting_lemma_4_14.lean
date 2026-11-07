-- Prove2me | Theorems.Thm_EllipsoidFitting_lemma_4_14
-- name    : EllipsoidFitting.lemma_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:21.059588+00:00
-- url     : https://prove2.me/theorems/60c68c72-f68a-4f43-911b-beb2f19140e0
-- title:
--   Lemma 4.14 — scalar bounds $r\approx\frac md\frac1{1-\gamma}$, $s\approx1-2\gamma$, $u\approx-1+\gamma$
-- statement:
--   Fix $0<a\le b<1$ and a sequence $m=m(d)$ with $a\le\gamma_d:=2m(d)/d^2\le b$ for all large $d$, and let $v_1,\dots,v_{m(d)}\sim N(0,I_d/d)$ be independent. For every $\varepsilon>0$, with probability tending to $1$,
--   $$
--   \Bigl|\frac{r\,d(1-\gamma_d)}{m(d)}-1\Bigr|\le\varepsilon,\qquad|s-(1-2\gamma_d)|\le\varepsilon,\qquad|u-(-1+\gamma_d)|\le\varepsilon,
--   $$
--   i.e. $r=(1+o_d(1))\frac md\frac1{1-\gamma}$, $s=1-2\gamma+o_d(1)$, $u=-1+\gamma+o_d(1)$, simultaneously.
--
--   In particular $s^2-ru\ne0$ with high probability (Corollary 4.15), so Lemma 2.18 applies.
--
--   **Formalization Note** "With high probability" is: the measure of the event that one of the three bounds fails tends to $0$.
--
--   Differences from the source:
--   - reading: the range of m is not stated → every m(d) with a ≤ 2m(d)/d² ≤ b for all large d, for fixed 0 < a ≤ b < 1; reason: the paper's standing regime for these estimates: γ in a fixed compact subinterval of (0,1) (Lemma B.3, p.108; Lemma 5.11, p.65); Definitions 2.14/4.1 fix 0 < γ < 1
--   - reading: with high probability, … ± o_d(1) → for every ε > 0 the probability that one of the three bounds fails tends to 0; reason: the paper's convention (Notation, p.5: all probabilistic statements hold with probability 1 − o_d(1)); one event for the three scalars
--   - encoding: r = (1 + o_d(1))·m/d·1/(1 − γ) → |r·d(1 − γ)/m − 1| ≤ ε; reason: ratio form; m(d) ≥ 1 for large d since γ_d ≥ a > 0
--   - encoding: probability of an event → the measure of the complementary (bad) set under the product law, tending to 0; reason: outer measure needs no measurability proof; for measurable events it is the same statement
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), Lemma 4.14, p.47 (PDF p.49)

import Mathlib
import Definitions.Def_EllipsoidFitting_scalarR
import Definitions.Def_EllipsoidFitting_pointLaw

set_option autoImplicit false

namespace EllipsoidFitting

open MeasureTheory Filter Topology

/-- **Lemma 4.14 (scalar bounds).** de la Cerda, Potechin, Tulsiani, Xu, *Sharp Phase Transition
for Ellipsoid Fitting*, arXiv:2608.12415 (version of Nov 3, 2026), Lemma 4.14, p.47: "Let r, s, u
be the scalars defined above. Then, with high probability, r := 1T_m A−1 1m / d = (1 + od(1)) · m/d
· 1/(1 − γ), s := 1 + ηT A−1 1m / d = 1 − 2γ + od(1), and u := −1 + ηT A−1 η / d = −1 + γ + od(1)."

Fix `0 < a ≤ b < 1` and a sequence `m(d)` with `a ≤ γ_d := 2m(d)/d² ≤ b` for all large `d`.
For every `ε > 0`, the probability that one of
`|r · d(1 − γ_d)/m(d) − 1| ≤ ε`, `|s − (1 − 2γ_d)| ≤ ε`, `|u − (−1 + γ_d)| ≤ ε` fails tends to `0`.

**Formalization Note** The lemma does not state its range of `m`; the regime "γ in a fixed compact
subinterval of (0, 1)" is the paper's own standing hypothesis for these estimates (Lemma B.3,
p.108; Lemma 5.11, p.65), and Definitions 2.14/4.1 fix `0 < γ < 1`. "With high probability" is:
the probability of the complementary event tends to `0` (outer measure). The three estimates hold
simultaneously. `r = (1 + o(1)) · m/(d(1−γ))` is the ratio form. -/
theorem lemma_4_14 (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (m : ℕ → ℕ)
    (hm : ∀ᶠ d in atTop, a ≤ gammaRatio d (m d) ∧ gammaRatio d (m d) ≤ b)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun d => pointLaw d (m d)
      {v | ¬ (|scalarR v * ((d : ℝ) * (1 - gammaRatio d (m d))) / (m d : ℝ) - 1| ≤ ε ∧
              |scalarS v - (1 - 2 * gammaRatio d (m d))| ≤ ε ∧
              |scalarU v - (-1 + gammaRatio d (m d))| ≤ ε)}) atTop (𝓝 0) := by sorry

end EllipsoidFitting
