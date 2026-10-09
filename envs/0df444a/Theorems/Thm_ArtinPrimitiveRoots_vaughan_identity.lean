-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_vaughan_identity
-- name    : ArtinPrimitiveRoots.vaughan_identity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T16:42:27.592388+00:00
-- url     : https://prove2.me/theorems/bf5c703e-00b9-4f74-8100-70d32df27ca7
-- title:
--   Vaughan's identity (classical; used for Bombieri–Vinogradov)
-- statement:
--   For natural numbers $U, V$, as an identity of real arithmetic functions under Dirichlet convolution,
--
--   $$\Lambda = \Lambda_V + \mu_U * \log - \mu_U * \Lambda_V * 1 + (\Lambda - \Lambda_V) * (\delta - \mu_U * 1),$$
--
--   where $\Lambda_V = $ `trunc Λ V` and $\mu_U = $ `trunc μ U` are the truncations $\Lambda(n)\mathbf 1_{n \le V}$ and $\mu(n)\mathbf 1_{n \le U}$, $\log$ is `ArithmeticFunction.log`, $1$ is the constant function $\zeta$ (`ζ`), and $\delta$ is the unit of Dirichlet convolution (the `1` of the ring `ArithmeticFunction ℝ`).
--
--   Reference: Davenport, *Multiplicative Number Theory*, ch. 24 (Vaughan's identity). This is a step of the proof of the Bombieri–Vinogradov theorem, which OpenAI's *Primitive roots for every admissible integer base* (2026) applies at (12.16), p. 77.
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 77, step of the proof of the Bombieri–Vinogradov theorem (12.16)

import Mathlib
import Definitions.Def_ArtinBV

namespace ArtinPrimitiveRoots

open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius ArithmeticFunction.zeta

theorem vaughan_identity (U V : ℕ) :
    (Λ : ArithmeticFunction ℝ) =
      trunc Λ V + trunc (μ : ArithmeticFunction ℝ) U * ArithmeticFunction.log
        - trunc (μ : ArithmeticFunction ℝ) U * trunc Λ V * (ζ : ArithmeticFunction ℝ)
        + (Λ - trunc Λ V) * (1 - trunc (μ : ArithmeticFunction ℝ) U * (ζ : ArithmeticFunction ℝ)) := by
  sorry

end ArtinPrimitiveRoots
