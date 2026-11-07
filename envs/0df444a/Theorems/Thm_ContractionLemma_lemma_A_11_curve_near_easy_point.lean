-- Prove2me | Theorems.Thm_ContractionLemma_lemma_A_11_curve_near_easy_point
-- name    : ContractionLemma.lemma_A_11_curve_near_easy_point
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:00:23.3923+00:00
-- url     : https://prove2.me/theorems/52929d8f-b58c-40af-b34a-310a74f0aa36
-- title:
--   Lemma A.11 — the curve near an easy point
-- statement:
--   Let $t\in\mathcal E\setminus\{-L\}$ and $\alpha=2L$. Then:
--
--   1. every entry of $W(t+\alpha z)$ is a polynomial in $z$ whose coefficients are rationals with odd denominators;
--   2. if $y-x\ne t$, every coefficient of $W_{xy}(t+\alpha z)$ is divisible by $2^{a+1-v_2(t-(y-x))}$, which is at least $2$; in particular every crossing entry is divisible by $2$;
--   3. the on-shift entries are
--   $$
--   W_{x,x+t}(t+\alpha z)=c_t\,\pi(z),\qquad \pi(z)=\prod_{s\in S\setminus\{t\}}\Big(1+\frac{\alpha z}{t-s}\Big),
--   $$
--   a polynomial in $z$ with constant term $1$. Moreover, $c_t$ is a ratio of odd numbers.
--
--   This is why, modulo a power of $2$, wires between groups can be expanded and truncated near an easy point.
--
--   **Formalization Note** "$q$ is divisible by $2^k$" is $q=0$ or $v_2(q)\ge k$. A crossing entry joins a row and a column vertex in different level-$v_2(t)$ groups of a packing with orientation; this clause carries orientation as a hypothesis, as the proof does.
--
--   Differences from the source:
--   - encoding: v₂(0) = ∞ → q = 0 or k ≤ v₂(q) for "divisible by 2^k"; reason: Mathlib sets padicValRat 2 0 = 0, so the zero case is stated separately
--   - reading: every crossing entry is divisible by 2 → an entry of one packet whose row vertex and column vertex have different level-v₂(t) symbols, under the orientation of Lemma A.9(a) as a hypothesis of that clause; reason: crossings are defined for the level-i grouping of Lemma A.9 (p.64), and the proof uses its orientation
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Lemma A.11, p.64; proof pp.87–88

import Mathlib
import Definitions.Def_ContractionLemma_kernel
import Definitions.Def_ContractionLemma_Placement
import Definitions.Def_ContractionLemma_Packing
import Definitions.Def_ContractionLemma_zoom

set_option autoImplicit false

namespace ContractionLemma

open Polynomial

/-- **Lemma A.11 (The curve near an easy point)** — Gajulapalli, *The Contraction Lemma Beyond
ETH* (manuscript, sha256 049caea1…), p.64 (PDF p.67); proof pp.87–88.

Let `t ∈ E \ {−L}` and `α = 2L`. Then:
(a) every entry of `W(t + αz)` is a polynomial in `z` whose coefficients are rationals with odd
denominators;
(b) if `y − x ≠ t`, every coefficient of `W_{xy}(t + αz)` is divisible by
`2^{a+1−v₂(t−(y−x))}`, which is at least `2`; in particular every crossing entry (row vertex and
column vertex in different level-`v₂(t)` groups of a packing with orientation) is divisible by
`2`;
(c) the on-shift entries are `W_{x,x+t}(t + αz) = c_t π(z)`, with `π(z) = ∏_{s∈S\{t}} (1 +
αz/(t − s))`, a polynomial with constant term `1`; moreover `c_t` is a ratio of odd numbers.

**Formalization Note.** "`q` is divisible by `2^k`" is `q = 0 ∨ k ≤ v₂(q)` (`v₂(0) = ∞`);
"odd denominator" is `¬ 2 ∣ q.den`; "a ratio of odd numbers" is: numerator and denominator in
lowest terms are odd. The entries are those of the shift curve of any packing; entries between
packets are `0`. -/
theorem lemma_A_11_curve_near_easy_point {U W E : Type*} [DecidableEq E] (rowOf : E → U)
    (colOf : E → W) (a : ℕ) (pk : Packing U W E a) (t : ℤ) (ht : t ∈ gridS a) (ht0 : t ≠ 0)
    (htL : t ≠ -(2 ^ a : ℤ)) :
    (∀ e f k, ¬ 2 ∣ (((pk.wiring e f).comp (C (t : ℚ) + C (alpha a) * X)).coeff k).den) ∧
    (∀ e f, pk.packet e = pk.packet f → (pk.slot f : ℤ) - (pk.slot e : ℤ) ≠ t →
      1 ≤ (a : ℤ) + 1 - padicValInt 2 (t - ((pk.slot f : ℤ) - (pk.slot e : ℤ))) ∧
      ∀ k, ((pk.wiring e f).comp (C (t : ℚ) + C (alpha a) * X)).coeff k = 0 ∨
        (a : ℤ) + 1 - padicValInt 2 (t - ((pk.slot f : ℤ) - (pk.slot e : ℤ))) ≤
          padicValRat 2 (((pk.wiring e f).comp (C (t : ℚ) + C (alpha a) * X)).coeff k)) ∧
    (∀ i : Fin a, (i : ℕ) = padicValInt 2 t → pk.Orientation rowOf colOf →
      ∀ e f, pk.packet e = pk.packet f → pk.rowLabel (rowOf e) i ≠ pk.colLabel (colOf f) i →
      ∀ k, ((pk.wiring e f).comp (C (t : ℚ) + C (alpha a) * X)).coeff k = 0 ∨
        1 ≤ padicValRat 2 (((pk.wiring e f).comp (C (t : ℚ) + C (alpha a) * X)).coeff k)) ∧
    (∀ e f, pk.packet e = pk.packet f → (pk.slot f : ℤ) = (pk.slot e : ℤ) + t →
      (pk.wiring e f).comp (C (t : ℚ) + C (alpha a) * X) = C (shiftConst a t) * piPoly a t) ∧
    (piPoly a t).coeff 0 = 1 ∧
    ¬ 2 ∣ (shiftConst a t).num ∧ ¬ 2 ∣ (shiftConst a t).den := by sorry

end ContractionLemma
