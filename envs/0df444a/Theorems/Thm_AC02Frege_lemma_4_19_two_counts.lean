-- Prove2me | Theorems.Thm_AC02Frege_lemma_4_19_two_counts
-- name    : AC02Frege.lemma_4_19_two_counts
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:51:46.882522+00:00
-- url     : https://prove2.me/theorems/b9a64ff2-7783-4212-8855-6d5ca8199a31
-- title:
--   Lemma 4.19 — the two counts needed for the dimension argument
-- statement:
--   Fix $0<c<1$ and let $F$ be a CNF on $n$ variables with no PC refutation of degree $D=\lfloor cn\rfloor$; let $\ell$ be odd, $N=n\ell$, $a\ge1$, and take
--   $$
--   Q=\lfloor cn/16\rfloor,\qquad K=\bigl\lfloor N/2-an\sqrt\ell\bigr\rfloor .\tag{31}
--   $$
--   Whenever $K\ge0$ (that is, $N/2-an\sqrt\ell\ge0$),
--   $$
--   h\ge2^{-n}M_N(K),\tag{32}
--   $$
--   $$
--   \varepsilon\le\exp\bigl[-(ca^2/8-\log2)\,n\bigr].\tag{33}
--   $$
--   Taking $ca^2/8\ge2\log2+12$ therefore gives
--   $$
--   \frac{\varepsilon M_N(K)}{h}\le e^{-12n}.\tag{34}
--   $$
--
--   These two counts make the coefficient-degree restriction almost free relative to the available room $h$ for the multiplier.
--
--   Differences from the source:
--   - encoding: ℓ odd, m = (ℓ − 1)/2 (standing assumption of §4) → hypothesis Odd ℓ, m = ℓ / 2; reason: same instances
--   - generalization: F of width at most w (setting of §4.4) → every CNF F with no PC refutation of degree ⌊cn⌋; reason: neither count involves the width; specializes to the source
--   - encoding: "whenever K ≥ 0" for K = ⌊N/2 − an√ℓ⌋ → hypothesis 0 ≤ N/2 − an√ℓ, K the natural-number floor; reason: for a nonnegative argument the natural floor is the integer floor
--   - encoding: log → Real.log (natural logarithm); reason: the constants 2 log 2 and log 2 come from e^{−…} and 2^n
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Lemma 4.19, (31)–(34), p.26; proof p.26 and App. C, p.46

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_PC
import Definitions.Def_AC02Frege_lift
import Definitions.Def_AC02Frege_majorityExpansion
import Definitions.Def_AC02Frege_rankCounts

namespace AC02Frege

open MvPolynomial LiftSAParity

/-- Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret, *Progress on AC0[2]-Frege Lower Bounds*, manuscript (sha256 88d149fa…), Lemma 4.19, (32)–(34), p.26 (the two counts needed for the dimension argument), in the
setting of §4.4 (p.26): `0 < c < 1`, `F` has no PC refutation of degree `D = ⌊cn⌋`, `ℓ` odd,
`N = nℓ`, and the choices (31) `Q = ⌊cn/16⌋`, `K = ⌊N/2 − an√ℓ⌋` with `a ≥ 1`. Whenever
`K ≥ 0` (i.e. `N/2 − an√ℓ ≥ 0`): `h ≥ 2^{−n} M_N(K)` (32), `ε ≤ exp[−(ca²/8 − log 2) n]` (33),
and if `ca²/8 ≥ 2 log 2 + 12` then `ε M_N(K)/h ≤ e^{−12n}` (34).

**Formalization Note** `log` is the natural logarithm. The width bound `w` of §4.4 is not
assumed (the counts do not depend on it). -/
theorem lemma_4_19_two_counts {n ℓ : ℕ} (hℓ : Odd ℓ) (c a : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (ha : 1 ≤ a) (F : CNF (Fin n)) (hF : ¬ PCDerivable F ⌊c * n⌋₊ 1)
    (hK : 0 ≤ ((n * ℓ : ℕ) : ℝ) / 2 - a * n * Real.sqrt ℓ) :
    let D := ⌊c * n⌋₊
    let Q := ⌊c * n / 16⌋₊
    let K := ⌊((n * ℓ : ℕ) : ℝ) / 2 - a * n * Real.sqrt ℓ⌋₊
    (monoCount (n * ℓ) K : ℝ) / 2 ^ n ≤ (hThresh F ℓ D K : ℝ) ∧
    epsExcl n ℓ Q K ≤ Real.exp (-(c * a ^ 2 / 8 - Real.log 2) * n) ∧
    (2 * Real.log 2 + 12 ≤ c * a ^ 2 / 8 →
      epsExcl n ℓ Q K * (monoCount (n * ℓ) K : ℝ) / (hThresh F ℓ D K : ℝ)
        ≤ Real.exp (-12 * n)) := by sorry

end AC02Frege
