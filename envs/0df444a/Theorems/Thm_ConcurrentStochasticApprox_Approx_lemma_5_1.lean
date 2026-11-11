-- Prove2me | Theorems.Thm_ConcurrentStochasticApprox_Approx_lemma_5_1
-- name    : ConcurrentStochasticApprox.Approx.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:11.713485+00:00
-- url     : https://prove2.me/theorems/ab9f60ea-34fa-4a33-b56c-df64de960afb
-- title:
--   Lemma 5.1 — closure of $F(\ell,B)$ and polynomial-time exact arithmetic
-- statement:
--   If $x\in F(\ell_1,B_1)$ and $y\in F(\ell_2,B_2)$, then
--   1. $x+y,\ x-y\in F(\ell_1+\ell_2,\max\{B_1,B_2\})$;
--   2. $x\cdot y\in F(\ell_1\ell_2,\max\{B_1,B_2\}+1)$;
--   3. addition, subtraction and multiplication, together with the comparison $x<y$, are performed in polynomial time with respect to the input size.
--
--   In item 3, polynomial-time machines map the binary encodings of representations of $x$ and $y$ to an encoding of a representation of the result satisfying the size bounds of items 1–2, and decide $x<y$.
--
--   Exact arithmetic with polynomial-size representations is what makes the verifier of witnesses exact.
--
--   Differences from the source:
--   - reading: all operations "can be performed in polynomial time with respect to the input size" → Cook-machine polynomial-time functions on the binary encodings of the two representations; the arithmetic functions output a representation that meets the size bounds of the closure clause; comparison outputs the bit [x < y]; reason: the closure clause gives the representations computed in the source proof (concatenation, sign flip, pairwise products); this reading is not weaker than the statement
-- source:
--   Ali Asadi, Krishnendu Chatterjee, The Computational Complexity of Concurrent Stochastic Games: Exact Value and Approximation, STOC 2027 submission #285 (October 2026), SHA-256 5cff187cf6b230b3bdfe540f2832f824d1ddb6acb43239fbf469d37c43b0d461, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/285.pdf, Lemma 5.1, printed p. 11 (PDF p. 13)

import Mathlib
import Definitions.Def_ConcurrentStochasticApprox_Approx_PowerSeries
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding
open Finset NetworkEquilibriumCLS.LinearNash

namespace ConcurrentStochasticApprox.Approx

/-- **Lemma 5.1.** If `x ∈ F(ℓ₁, B₁)` and `y ∈ F(ℓ₂, B₂)`, then `x + y, x - y ∈ F(ℓ₁ + ℓ₂, max(B₁, B₂))`
and `x · y ∈ F(ℓ₁ · ℓ₂, max(B₁, B₂) + 1)`; moreover addition, subtraction and multiplication (with
outputs meeting these size bounds) and the comparison `x < y` are computed in polynomial time on
the binary power-series encodings. -/
theorem lemma_5_1 :
    (∀ (ℓ₁ B₁ ℓ₂ B₂ : ℕ) (x y : ℝ), x ∈ F ℓ₁ B₁ → y ∈ F ℓ₂ B₂ →
      x + y ∈ F (ℓ₁ + ℓ₂) (max B₁ B₂) ∧ x - y ∈ F (ℓ₁ + ℓ₂) (max B₁ B₂) ∧
      x * y ∈ F (ℓ₁ * ℓ₂) (max B₁ B₂ + 1)) ∧
    (∃ add : List Bool → List Bool, CookPvsNP.PolyTimeComputable add ∧
      ∀ (ℓ₁ B₁ ℓ₂ B₂ : ℕ) (u v : PSNum), InF ℓ₁ B₁ u → InF ℓ₂ B₂ v →
        ∃ w : PSNum, add (encPS u ++ encPS v) = encPS w ∧ InF (ℓ₁ + ℓ₂) (max B₁ B₂) w ∧
          psVal w = psVal u + psVal v) ∧
    (∃ sub : List Bool → List Bool, CookPvsNP.PolyTimeComputable sub ∧
      ∀ (ℓ₁ B₁ ℓ₂ B₂ : ℕ) (u v : PSNum), InF ℓ₁ B₁ u → InF ℓ₂ B₂ v →
        ∃ w : PSNum, sub (encPS u ++ encPS v) = encPS w ∧ InF (ℓ₁ + ℓ₂) (max B₁ B₂) w ∧
          psVal w = psVal u - psVal v) ∧
    (∃ mul : List Bool → List Bool, CookPvsNP.PolyTimeComputable mul ∧
      ∀ (ℓ₁ B₁ ℓ₂ B₂ : ℕ) (u v : PSNum), InF ℓ₁ B₁ u → InF ℓ₂ B₂ v →
        ∃ w : PSNum, mul (encPS u ++ encPS v) = encPS w ∧ InF (ℓ₁ * ℓ₂) (max B₁ B₂ + 1) w ∧
          psVal w = psVal u * psVal v) ∧
    (∃ lt : List Bool → List Bool, CookPvsNP.PolyTimeComputable lt ∧
      ∀ u v : PSNum, lt (encPS u ++ encPS v) = [decide (psVal u < psVal v)]) := by sorry

end ConcurrentStochasticApprox.Approx
