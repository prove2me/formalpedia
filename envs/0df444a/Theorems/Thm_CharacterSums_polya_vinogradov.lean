-- Prove2me | Theorems.Thm_CharacterSums_polya_vinogradov
-- name    : CharacterSums.polya_vinogradov
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T02:25:11.59203+00:00
-- url     : https://prove2.me/theorems/b299fdd2-c85a-4bd9-b2f4-02ce50c6b4ad
-- title:
--   The Polya-Vinogradov inequality for primitive Dirichlet characters
-- statement:
--   The **Pólya–Vinogradov inequality** bounds the partial sums of a primitive Dirichlet character,
--   uniformly in the length of the sum.
--
--   $$\Big|\sum_{m < t} \chi(m)\Big| \;\le\; \sqrt{f}\,\bigl(1 + \log f\bigr)$$
--
--   Here $\chi$ is a primitive Dirichlet character modulo $f \ge 2$, taking values in $\mathbb{C}$, and
--   $t$ is an arbitrary nonnegative integer. The essential point is that the bound does not depend on
--   $t$: although the sum has $t$ terms each of modulus $1$, the cancellation among the character
--   values keeps every partial sum below $\sqrt{f}(1+\log f)$, which is $O(\sqrt f \log f)$ regardless
--   of how long the range is.
--
--   The inequality is one of the basic tools of analytic number theory. It gives the classical bound on
--   the least quadratic non-residue, underlies character-sum estimates in the circle method, and is the
--   standard input wherever a character sum over an interval must be controlled. The proof is the
--   classical one: expand each character value by Gauss-sum inversion, exchange the order of summation,
--   and estimate the resulting geometric sums against the distance to the nearest integer.
--
--   **Formalization note.** The statement is written against Mathlib's `DirichletCharacter`, with
--   `χ.IsPrimitive` the primitivity hypothesis and the sum taken over `Finset.range t` with the argument
--   cast into `ZMod f`. No auxiliary definitions are required beyond Mathlib.
-- source:
--   Polya-Vinogradov inequality. Lean proof from the Salt project by Jason Hickey, Salt/BV/PolyaVinogradov.lean (https://github.com/jyh/salt, Apache-2.0).

import Mathlib

namespace CharacterSums

/-- The Pólya–Vinogradov inequality: for a primitive Dirichlet character `χ` modulo `f ≥ 2`,
the partial character sums are bounded uniformly in the length `t`. -/
theorem polya_vinogradov {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) (t : ℕ) :
    ‖∑ m ∈ Finset.range t, χ (m : ZMod f)‖ ≤ Real.sqrt f * (1 + Real.log f) := by
  sorry

end CharacterSums
