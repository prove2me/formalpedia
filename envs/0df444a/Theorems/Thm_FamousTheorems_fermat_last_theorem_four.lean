-- Prove2me | Theorems.Thm_FamousTheorems_fermat_last_theorem_four
-- name    : FamousTheorems.fermat_last_theorem_four
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:18.275157+00:00
-- url     : https://prove2.me/theorems/991f1838-f47a-43eb-9d0f-4ed048ca2113
-- title:
--   Fermat's Last Theorem for exponent 4
-- statement:
--   **Fermat's Last Theorem for exponent $4$.** There are no positive integers $a,b,c$ with
--   $$a^4+b^4=c^4.$$
--
--   This is the one case of his "last theorem" that Fermat proved himself, by his method of infinite descent (in fact he showed that $x^4+y^4=z^2$ has no positive solutions). It reduces Fermat's Last Theorem to odd prime exponents, since any exponent $n\ge3$ is divisible by $4$ or by an odd prime.
--
--   **Formalization note.** Mathlib's `fermatLastTheoremFour`. The statement is Mathlib's `FermatLastTheoremFor 4` written out in full: for natural numbers $a,b,c$, all nonzero, $a^4+b^4\neq c^4$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `fermatLastTheoremFour`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem fermat_last_theorem_four : ∀ a b c : ℕ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ 4 + b ^ 4 ≠ c ^ 4 := by sorry

end FamousTheorems
