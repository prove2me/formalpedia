-- Prove2me | Theorems.Thm_AC02Frege_lemma_4_8_coeff_degree_scalar
-- name    : AC02Frege.lemma_4_8_coeff_degree_scalar
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:50:21.315354+00:00
-- url     : https://prove2.me/theorems/a1ac4378-f551-4790-bd91-72d0e40138a4
-- title:
--   Lemma 4.8 — coefficient degree in scalar coordinates
-- statement:
--   Let $\ell$ be odd. If $p=\sum_T c_Tx_T\ne0$ is a multilinear polynomial in the lifted variables, then
--   $$
--   \beta(p)=\max\{|J(T)|: c_T\ne0\},
--   $$
--   where $J(T)$ is the set of blocks in which $x_T$ selects more than half the bits. Consequently $p\in W_Q$ if and only if $c_T=0$ whenever $|J(T)|>Q$.
--
--   So the restriction $\beta(f)\le Q$ on the multiplier is a set of coordinate restrictions on its scalar coefficients.
--
--   Differences from the source:
--   - encoding: ℓ odd, m = (ℓ − 1)/2 (standing assumption of §4) → hypothesis Odd ℓ, m = ℓ / 2; reason: same instances
--   - encoding: p = Σ_T c_T x_T with c_T ≠ 0 → multilinear p; its monomials s ∈ p.support, with T = s.support; reason: a multilinear monomial is determined by its support
--   - generalization: "Consequently p ∈ W_Q iff …" under p ≠ 0 → the equivalence for every multilinear p, including p = 0; reason: for p = 0 both sides hold (β(0) = −∞ and there is no monomial); specializes to the source
--   - encoding: β(p) with β(0) = −∞ → coeffDeg p : WithBot ℕ; reason: same values
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Lemma 4.8, p.22

import Mathlib
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_lift
import Definitions.Def_AC02Frege_majorityExpansion

namespace AC02Frege

open MvPolynomial

/-- Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret, *Progress on AC0[2]-Frege Lower Bounds*, manuscript (sha256 88d149fa…), Lemma 4.8, p.22 (coefficient degree in scalar coordinates): for odd `ℓ`, if
`p = Σ_T c_T x_T ≠ 0` then `β(p) = max{|J(T)| : c_T ≠ 0}`; consequently `p ∈ W_Q` iff `c_T = 0`
whenever `|J(T)| > Q`.

**Formalization Note** `p` is multilinear, so its monomials `s` are the `x_T` with `T = s.support`
and `c_T ≠ 0` means `s ∈ p.support`. The second clause is stated for every multilinear `p`
(for `p = 0` both sides hold). -/
theorem lemma_4_8_coeff_degree_scalar {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hp : IsMultilinear p) :
    (p ≠ 0 → coeffDeg p = ((p.support.sup (fun s => (heavyBlocks s.support).card) : ℕ) :
      WithBot ℕ)) ∧
    ∀ Q : ℕ, p ∈ WQ n ℓ Q ↔ ∀ s ∈ p.support, (heavyBlocks s.support).card ≤ Q := by sorry

end AC02Frege
