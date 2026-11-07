-- Prove2me | Theorems.Thm_AC02Frege_lemma_4_10_multiplication_majority
-- name    : AC02Frege.lemma_4_10_multiplication_majority
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:50:54.65145+00:00
-- url     : https://prove2.me/theorems/5ed798a5-34ec-4541-a9c4-f24442afa046
-- title:
--   Lemma 4.10 — multiplication in majority coordinates
-- statement:
--   Let $\ell$ be odd, $F$ a CNF on $n$ variables and $D$ an integer. For all polynomials $p,v$ in the lifted variables,
--   $$
--   \beta(pv)\le\beta(p)+\deg_x v .
--   $$
--   Moreover,
--   $$
--   p\in\widehat C_D,\quad \beta(p)+\deg_x v\le D\ \Longrightarrow\ pv\in\widehat C_D .
--   $$
--   Both statements hold with $\deg_x v$ replaced by the number of blocks on which $v$ depends.
--
--   This is the lifted replacement of Fact 2.5: multiplication is controlled by the coefficient degree of the known member and the ordinary degree of the factor.
--
--   Differences from the source:
--   - encoding: ℓ odd, m = (ℓ − 1)/2 (standing assumption of §4) → hypothesis Odd ℓ, m = ℓ / 2; reason: same instances
--   - encoding: polynomials over F2 identified with functions on the cube; products of functions → MvPolynomial over ZMod 2; products multilinearized by ML (membership in Ĉ_D and β depend only on ML p); reason: Definition 2.1 identifies a function with its multilinear polynomial; no instance changes
--   - encoding: deg_x v; the number of blocks on which v depends → totalDegree (ML v); the number of blocks i some x_{i,a} of which occurs in ML v; reason: a function depends on a variable iff it occurs in its multilinear polynomial
--   - encoding: β with β(0) = −∞, sums β(p) + d → WithBot ℕ with ⊥ + d = ⊥; reason: same values
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Lemma 4.10, pp.22–23

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_PC
import Definitions.Def_AC02Frege_lift
import Definitions.Def_AC02Frege_majorityExpansion

namespace AC02Frege

open MvPolynomial LiftSAParity

/-- Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret, *Progress on AC0[2]-Frege Lower Bounds*, manuscript (sha256 88d149fa…), Lemma 4.10, pp.22–23 (multiplication in majority coordinates): for odd `ℓ` and all
polynomials `p, v` in the lifted variables, `β(pv) ≤ β(p) + deg_x v`; moreover
`p ∈ Ĉ_D, β(p) + deg_x v ≤ D ⟹ pv ∈ Ĉ_D`; both statements hold with `deg_x v` replaced by the
number of blocks on which `v` depends.

**Formalization Note** `pv` is the product of functions (membership and `β` depend only on
`ML (p * v)`); `deg_x v` is the degree of the multilinear polynomial `ML v`; `β` is in
`WithBot ℕ` with `⊥ + d = ⊥`. -/
theorem lemma_4_10_multiplication_majority {n ℓ : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n)) (D : ℕ) :
    (∀ p v : MvPolynomial (Fin n × Fin ℓ) (ZMod 2),
      coeffDeg (p * v) ≤ coeffDeg p + ((ML v).totalDegree : WithBot ℕ)) ∧
    (∀ p v : MvPolynomial (Fin n × Fin ℓ) (ZMod 2), p ∈ CHat F ℓ D →
      coeffDeg p + ((ML v).totalDegree : WithBot ℕ) ≤ (D : WithBot ℕ) → p * v ∈ CHat F ℓ D) ∧
    (∀ p v : MvPolynomial (Fin n × Fin ℓ) (ZMod 2),
      coeffDeg (p * v) ≤ coeffDeg p + ((blocksOf v : ℕ) : WithBot ℕ)) ∧
    (∀ p v : MvPolynomial (Fin n × Fin ℓ) (ZMod 2), p ∈ CHat F ℓ D →
      coeffDeg p + ((blocksOf v : ℕ) : WithBot ℕ) ≤ (D : WithBot ℕ) → p * v ∈ CHat F ℓ D) := by sorry

end AC02Frege
