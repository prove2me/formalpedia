-- Prove2me | Theorems.Thm_BddExp3SUM_coefficient_cap
-- name    : BddExp3SUM.coefficient_cap
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:59:37.338209+00:00
-- url     : https://prove2.me/theorems/c4464823-2c05-4678-8994-0e21e333d3c0
-- title:
--   §6: rejection sampling with $24t$ attempts for $t$ coefficients aborts with probability at most $1/12$, coupled with uniform coefficients
-- statement:
--   Let $M\ge2$, $C=\lceil\log_2M\rceil$, and draw $24t$ independent attempts of $C$ fair bits each, rejecting values at least $M$. Then an accepted coefficient needs at most two attempts in expectation, $2^C/M\le2$; fewer than $t$ values are accepted with probability at most $1/12$; and for every set $E$ of vectors in $\mathbb Z_M^t$,
--
--   $$\mathbb P[\text{at least }t\text{ accepted and the first }t\text{ accepted lie in }E]\ge\frac{|E|}{M^t}-\frac1{12}.$$
--
--   The last clause is the coupling with ideal uniform coefficients: the proof of Theorem 1 subtracts $1/12$ from the probability of the good event.
--
--   Differences from the source:
--   - generalization: t = rℓ coefficients for a profile subinstance → every t; reason: the source’s t is a special case
--   - encoding: "An accepted coefficient needs at most two attempts in expectation" → 2^C/M ≤ 2; reason: the number of attempts per accepted coefficient is geometric with success probability M/2^C, so its mean is 2^C/M
--   - encoding: "Coupling with unlimited independent uniform generation" → a lower bound on the probability of each event E of coefficient vectors; reason: this is the content of the coupling that the proof uses
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Truly Subquadratic 3SUM over Every Bounded-Exponent Abelian Group, STOC 2027 submission (manuscript sha256 19546c9a…), §6, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_BddExp3SUM_Instance
import Definitions.Def_BddExp3SUM_Hash
import Definitions.Def_BddExp3SUM_CoefficientSampler

namespace BddExp3SUM

/-- The coefficient cap, §6, p.7 (Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission, manuscript sha256
19546c9a…): `C` fair bits per attempt, rejecting values at least `M`, and `24t` attempts for `t`
coefficients (`t = rℓ` in the paper).

**Formalization Note.** The first clause is "at most two attempts in expectation", since one attempt is
accepted with probability `M/2^C`. The second is the abort bound. The third is the coupling with ideal
uniform coefficients, the form the proof uses: for every set `E` of coefficient vectors, the capped
sampler produces a vector in `E` with probability at least `|E|/M^t - 1/12`. -/
theorem coefficient_cap {M : ℕ} [NeZero M] (hM : 2 ≤ M) (t : ℕ) :
    (2 : ℝ) ^ C M / M ≤ 2 ∧
    uniformProb (fun a : Fin (24 * t) → Fin (C M) → Bool => (accepted M a).length < t) ≤ 1 / 12 ∧
    ∀ E : Finset (Fin t → ZMod M),
      (E.card : ℝ) / (M : ℝ) ^ t - 1 / 12 ≤
        uniformProb (fun a : Fin (24 * t) → Fin (C M) → Bool =>
          ∃ w ∈ E, firstCoeffs (accepted M a) t = some w) := by sorry

end BddExp3SUM
