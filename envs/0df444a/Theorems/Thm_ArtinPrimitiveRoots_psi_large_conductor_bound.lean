-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_psi_large_conductor_bound
-- name    : ArtinPrimitiveRoots.psi_large_conductor_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T16:42:30.557463+00:00
-- url     : https://prove2.me/theorems/b17838ac-829a-4f78-96b1-3156bd543062
-- title:
--   Large-sieve bound for ψ(X, χ) over primitive characters of large conductor (classical; used for Bombieri–Vinogradov)
-- statement:
--   For all reals $A, \eta > 0$ there is $C$ such that for every natural $X \ge 2$ and every natural $R \ge 1$ with $R \le X^{1/2 - \eta}$,
--
--   $$\sum_{R < d \le 2R} \frac{1}{\varphi(d)} \sum_{\chi \bmod d \text{ primitive}} |\psi(X, \chi)| \;\le\; C X\Bigl(\frac{(\log X)^4}{R} + (\log X)^{-A}\Bigr),$$
--
--   where $\psi(X, \chi) = $ `psiChar χ X` $= \sum_{n \le X}\Lambda(n)\chi(n)$ and the inner sum runs over `primChars d`. $C$ depends only on $A$ and $\eta$.
--
--   **Formalization note.** Davenport's estimate is the sum over all $d \le Q$ of $\frac{d}{\varphi(d)}\max_{Y \le X}|\psi(Y, \chi)|$, bounded by $(X + X^{5/6}Q + X^{1/2}Q^2)(\log QX)^4$. Here the sum is over one dyadic range of conductors, at the single point $X$, weighted by $1/\varphi(d)$, and the bound is specialised to $Q \le X^{1/2 - \eta}$. That is the form in which the dyadic ranges are summed in the proof of the Bombieri–Vinogradov theorem.
--
--   Reference: Davenport, *Multiplicative Number Theory*, ch. 28. This is a step of the proof of the Bombieri–Vinogradov theorem, which OpenAI's *Primitive roots for every admissible integer base* (2026) applies at (12.16), p. 77.
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 77, step of the proof of the Bombieri–Vinogradov theorem (12.16)

import Mathlib
import Definitions.Def_ArtinBV

namespace ArtinPrimitiveRoots

open Finset Real

theorem psi_large_conductor_bound (A η : ℝ) (hA : 0 < A) (hη : 0 < η) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∀ R : ℕ, 1 ≤ R → (R : ℝ) ≤ (X : ℝ) ^ (1 / 2 - η) →
      ∑ d ∈ Ioc R (2 * R), (1 / (d.totient : ℝ)) * ∑ χ ∈ primChars d, ‖psiChar χ X‖
        ≤ C * X * (log X ^ 4 / R + log X ^ (-A)) := by
  sorry

end ArtinPrimitiveRoots
