-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_psi_prime_number_theorem
-- name    : ArtinPrimitiveRoots.psi_prime_number_theorem
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T16:42:12.632977+00:00
-- url     : https://prove2.me/theorems/602312bc-4b5d-419c-bc5f-dcb64e83f854
-- title:
--   Prime number theorem for ψ with error term (X (log X)^(-A)) (classical; used for Bombieri–Vinogradov)
-- statement:
--   For every real $A > 0$ there is $C$ such that for every natural $X \ge 2$,
--
--   $$\Bigl|\sum_{0 < n \le X}\Lambda(n) - X\Bigr| \le C\,X(\log X)^{-A}.$$
--
--   That is, $\psi(X) = X + O_A\bigl(X(\log X)^{-A}\bigr)$, where $\Lambda$ is Mathlib's von Mangoldt function. This is the case $q = 1$ of the Siegel–Walfisz theorem; in the proof it is deduced from the published prime-counting form `ArtinPrimitiveRoots.siegel_walfisz`.
--
--   Reference: Davenport, *Multiplicative Number Theory*, ch. 18 (the prime number theorem with classical error term). This is a step of the proof of the Bombieri–Vinogradov theorem, which OpenAI's *Primitive roots for every admissible integer base* (2026) applies at (12.16), p. 77.
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 77, step of the proof of the Bombieri–Vinogradov theorem (12.16)

import Mathlib

namespace ArtinPrimitiveRoots

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

theorem psi_prime_number_theorem (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → |(∑ n ∈ Ioc 0 X, Λ n) - X| ≤ C * (X * log X ^ (-A)) := by
  sorry

end ArtinPrimitiveRoots
