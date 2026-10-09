-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_psi_small_conductor_bound
-- name    : ArtinPrimitiveRoots.psi_small_conductor_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T16:42:47.419812+00:00
-- url     : https://prove2.me/theorems/f3731b95-55e2-4baa-bcb1-af3bf06be634
-- title:
--   Siegel–Walfisz bound for ψ(X, χ), small moduli (classical; used for Bombieri–Vinogradov)
-- statement:
--   For all reals $A, B > 0$ there is $C$ such that for every natural $X \ge 2$, every natural $d$ with $1 \le d \le (\log X)^B$, and every nontrivial Dirichlet character $\chi$ modulo $d$,
--
--   $$|\psi(X, \chi)| \le C\,X(\log X)^{-A},$$
--
--   where $\psi(X, \chi) = $ `psiChar χ X` $= \sum_{n \le X}\Lambda(n)\chi(n)$. $C$ depends only on $A$ and $B$.
--
--   This is the character form of the Siegel–Walfisz theorem. In the proof it is deduced from the published prime-counting form `ArtinPrimitiveRoots.siegel_walfisz`.
--
--   Reference: Davenport, *Multiplicative Number Theory*, ch. 22. This is a step of the proof of the Bombieri–Vinogradov theorem, which OpenAI's *Primitive roots for every admissible integer base* (2026) applies at (12.16), p. 77.
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 77, step of the proof of the Bombieri–Vinogradov theorem (12.16)

import Mathlib
import Definitions.Def_ArtinBV

namespace ArtinPrimitiveRoots

open Real

theorem psi_small_conductor_bound (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ log X ^ B →
      ∀ χ : DirichletCharacter ℂ d, χ ≠ 1 → ‖psiChar χ X‖ ≤ C * (X * log X ^ (-A)) := by
  sorry

end ArtinPrimitiveRoots
