-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_bombieri_vinogradov
-- name    : ArtinPrimitiveRoots.bombieri_vinogradov
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T09:27:18.611261+00:00
-- url     : https://prove2.me/theorems/dbd3ab85-7d0a-428f-82a1-40ed9790e616
-- title:
--   Bombieri–Vinogradov theorem, in the form applied in (12.16)
-- statement:
--   For all reals $A', \eta > 0$ there is $C$ such that for every real $Y \ge 2$ and every choice of residues $v : \mathbb N \to \mathbb N$ with $(v(q), q) = 1$ for all $q$,
--
--   $$\sum_{1 \le q < Y^{1/2 - \eta}}\Bigl|\pi(Y; q, v(q)) - \frac{\mathrm{Li}(Y)}{\varphi(q)}\Bigr| \le C\,Y(\log Y)^{-A'},$$
--
--   where $\pi(Y; q, v) = $ `primeCountingAP Y q v` counts the primes $p \le Y$ with $p \equiv v \pmod q$ and $\mathrm{Li}(Y) = $ `logIntegral Y` $= \int_2^Y dt/\log t$. $C$ depends only on $A'$ and $\eta$.
--
--   This is a classical result that Mathlib lacks; the paper applies it in the proof of Lemma 12.3.
--
--   **Formalization note.** The maximum over reduced classes $v \bmod q$ is encoded by quantifying over every choice function $v$ with $(v(q), q) = 1$; since $\pi(Y; q, v)$ depends only on $v \bmod q$ and the maximum is attained, this is equivalent. (At $q = 0$, which is outside the sum, the condition just forces $v(0) = 1$.)
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 77: “We use the prime-counting form of the Bombieri–Vinogradov theorem [3, 29]: for fixed $A', \eta > 0$, $\sum_{q < Y^{1/2-\eta}}\max_{(v,q)=1}\Bigl|\pi(Y; q, v) - \frac{\mathrm{Li}(Y)}{\varphi(q)}\Bigr| \ll_{A',\eta} Y(\log Y)^{-A'}$. (12.16) Here $\mathrm{Li}(Y) = \int_2^Y dt/\log t$.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 77, (12.16), the Bombieri–Vinogradov theorem as applied

import Mathlib
import Definitions.Def_ArtinSieve

namespace ArtinPrimitiveRoots

open Real

theorem bombieri_vinogradov (A' η : ℝ) (hA' : 0 < A') (hη : 0 < η) :
    ∃ C : ℝ, ∀ Y : ℝ, 2 ≤ Y → ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈Y ^ (1 / 2 - η)⌉₊).filter (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < Y ^ (1 / 2 - η)),
          |(primeCountingAP Y q (v q) : ℝ) - logIntegral Y / Nat.totient q| ≤
        C * (Y * log Y ^ (-A')) := by
  sorry

end ArtinPrimitiveRoots
