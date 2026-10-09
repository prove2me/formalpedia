-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_psi_bombieri_vinogradov
-- name    : ArtinPrimitiveRoots.psi_bombieri_vinogradov
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T16:42:40.740842+00:00
-- url     : https://prove2.me/theorems/6744b61a-9e9c-454b-a283-d7da0c6e3c81
-- title:
--   Bombieri–Vinogradov theorem for ψ(X; q, a) (classical; used for Bombieri–Vinogradov)
-- statement:
--   For all reals $A, \eta > 0$ there is $C$ such that for every natural $X \ge 2$ and every choice of residues $a : \mathbb N \to \mathbb N$ with $(a(q), q) = 1$ for all $q$,
--
--   $$\sum_{1 \le q \le X^{1/2 - \eta}}\Bigl|\psi(X; q, a(q)) - \frac{X}{\varphi(q)}\Bigr| \le C\,X(\log X)^{-A},$$
--
--   where $\psi(X; q, a) = $ `psiAP X q a` $= \sum_{n \le X,\ n \equiv a\ (q)}\Lambda(n)$. $C$ depends only on $A$ and $\eta$.
--
--   **Formalization note.** The textbook statement has $\max_{(a, q) = 1}$ and, in Davenport's form, also $\max_{Y \le X}$. Quantifying over every choice function $a$ is equivalent to the maximum over residues. The maximum over $Y \le X$ is dropped: the statement is at the single point $X$, which is all that the transfer to $\pi(Y; q, a)$ by partial summation needs, since it is applied at every $k \le Y$.
--
--   Reference: Davenport, *Multiplicative Number Theory*, ch. 28. This is a step of the proof of the Bombieri–Vinogradov theorem, which OpenAI's *Primitive roots for every admissible integer base* (2026) applies at (12.16), p. 77.
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 77, step of the proof of the Bombieri–Vinogradov theorem (12.16)

import Mathlib
import Definitions.Def_ArtinBV

namespace ArtinPrimitiveRoots

open Finset Real

theorem psi_bombieri_vinogradov (A η : ℝ) (hA : 0 < A) (hη : 0 < η) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∀ a : ℕ → ℕ, (∀ q, Nat.Coprime (a q) q) →
      ∑ q ∈ Icc 1 ⌊(X : ℝ) ^ (1 / 2 - η)⌋₊, |psiAP X q (a q) - X / q.totient|
        ≤ C * (X * log X ^ (-A)) := by
  sorry

end ArtinPrimitiveRoots
