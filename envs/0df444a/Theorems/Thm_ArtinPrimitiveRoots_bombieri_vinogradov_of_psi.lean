-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_bombieri_vinogradov_of_psi
-- name    : ArtinPrimitiveRoots.bombieri_vinogradov_of_psi
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T16:42:35.253983+00:00
-- url     : https://prove2.me/theorems/d45a468d-e832-489a-8625-349163a44150
-- title:
--   Bombieri–Vinogradov for primes from Bombieri–Vinogradov for ψ (partial summation; used for Bombieri–Vinogradov)
-- statement:
--   Suppose the Bombieri–Vinogradov theorem for $\psi$ holds: for all $A, \eta > 0$ there is $C$ with
--
--   $$\sum_{1 \le q \le X^{1/2 - \eta}}\Bigl|\psi(X; q, a(q)) - \frac{X}{\varphi(q)}\Bigr| \le C\,X(\log X)^{-A}$$
--
--   for every natural $X \ge 2$ and every choice of residues $a$ with $(a(q), q) = 1$, where $\psi(X; q, a) = $ `psiAP X q a`. Then for all $A', \eta > 0$ there is $C$ such that for every real $Y \ge 2$ and every choice of residues $v$ with $(v(q), q) = 1$,
--
--   $$\sum_{1 \le q < Y^{1/2 - \eta}}\Bigl|\pi(Y; q, v(q)) - \frac{\mathrm{Li}(Y)}{\varphi(q)}\Bigr| \le C\,Y(\log Y)^{-A'},$$
--
--   where $\pi(Y; q, v) = $ `primeCountingAP Y q v` and $\mathrm{Li}(Y) = $ `logIntegral Y` $= \int_2^Y dt/\log t$. The conclusion is exactly the published `ArtinPrimitiveRoots.bombieri_vinogradov`.
--
--   The passage from $\psi$ to $\pi$ is by partial summation, after removing prime powers. It is the standard deduction.
--
--   Reference: Davenport, *Multiplicative Number Theory*, ch. 28 (end) and ch. 22. This is a step of the proof of the Bombieri–Vinogradov theorem, which OpenAI's *Primitive roots for every admissible integer base* (2026) applies at (12.16), p. 77.
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 77, step of the proof of the Bombieri–Vinogradov theorem (12.16)

import Mathlib
import Definitions.Def_ArtinSieve
import Definitions.Def_ArtinBV

namespace ArtinPrimitiveRoots

open Finset Real

theorem bombieri_vinogradov_of_psi
    (h : ∀ A η : ℝ, 0 < A → 0 < η → ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∀ a : ℕ → ℕ,
      (∀ q, Nat.Coprime (a q) q) →
      ∑ q ∈ Icc 1 ⌊(X : ℝ) ^ (1 / 2 - η)⌋₊, |psiAP X q (a q) - X / q.totient|
        ≤ C * (X * log X ^ (-A)))
    (A' η : ℝ) (hA' : 0 < A') (hη : 0 < η) :
    ∃ C : ℝ, ∀ Y : ℝ, 2 ≤ Y → ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈Y ^ (1 / 2 - η)⌉₊).filter (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < Y ^ (1 / 2 - η)),
          |(primeCountingAP Y q (v q) : ℝ) - logIntegral Y / Nat.totient q| ≤
        C * (Y * log Y ^ (-A')) := by
  sorry

end ArtinPrimitiveRoots
