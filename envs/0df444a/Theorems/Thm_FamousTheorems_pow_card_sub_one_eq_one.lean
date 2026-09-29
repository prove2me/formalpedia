-- Prove2me | Theorems.Thm_FamousTheorems_pow_card_sub_one_eq_one
-- name    : FamousTheorems.pow_card_sub_one_eq_one
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T01:51:25.959993+00:00
-- url     : https://prove2.me/theorems/2dd12082-9d06-40d8-9c73-651aedf8e597
-- title:
--   Fermat's little theorem
-- statement:
--   **Fermat's little theorem.**
--
--   For a prime $p$ and $a \not\equiv 0 \pmod p$,
--   $$a^{\,p-1} \equiv 1 \pmod p .$$
--
--   Equivalently $a^p \equiv a$ for every $a$. The statement is that the multiplicative group of
--   $\mathbb{Z}/p\mathbb{Z}$ has order $p-1$, so Lagrange's theorem kills every element on raising to
--   that power — which is why the hypothesis is exactly $a \neq 0$, the condition for $a$ to lie in that
--   group at all.
--
--   Fermat announced it in a 1640 letter to Frénicle, characteristically without proof; Euler published
--   the first one in 1736 and later generalised it to $a^{\varphi(n)} \equiv 1$ for arbitrary modulus.
--   It is the basis of Fermat primality testing and, through its Euler generalisation, of RSA: the
--   decryption exponent works precisely because $a^{\varphi(n)} \equiv 1$.
--
--   The converse fails — the Carmichael numbers, of which $561$ is the smallest, satisfy the congruence
--   for every coprime base without being prime — which is why probabilistic primality tests need the
--   stronger Miller–Rabin refinement.
--
--   **Formalization note.** `ZMod p` is the integers mod $p$ and `Fact p.Prime` supplies the field
--   structure, so `a ≠ 0` is literally the unit condition. The result is Mathlib's
--   `ZMod.pow_card_sub_one_eq_one`.
-- source:
--   Listed in Mathlib's "1000 theorems" manifest (docs/1000.yaml); formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

theorem pow_card_sub_one_eq_one {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    a ^ (p - 1) = 1 := by sorry

end FamousTheorems
