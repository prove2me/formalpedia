-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_mertens_product
-- name    : ArtinPrimitiveRoots.mertens_product
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T09:27:21.145978+00:00
-- url     : https://prove2.me/theorems/fe3358fb-cb55-41dd-b18d-946e48527d97
-- title:
--   Mertens' product theorem, (11.5)
-- statement:
--   As the real $y \to \infty$,
--
--   $$V(y)\,\log y \to e^{-\gamma_E},\qquad V(y) = \prod_{p \le y}\Bigl(1 - \frac1p\Bigr) \ (\texttt{mertensProduct}\ y),$$
--
--   where $\gamma_E$ is Euler's constant (`Real.eulerMascheroniConstant`). That is, $V(y) \sim e^{-\gamma_E}/\log y$.
--
--   This is a classical result that Mathlib lacks; the paper uses it in §§11–12.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 72: “For the product $V(y)$ in (10.1), Mertens' theorem gives $V(y) \sim \frac{\exp(-\gamma_E)}{\log y}$, (11.5) where $\gamma_E$ is Euler's constant.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 72, (11.5), Mertens' product theorem

import Mathlib
import Definitions.Def_ArtinSieve

namespace ArtinPrimitiveRoots

open Real Filter Topology

theorem mertens_product :
    Tendsto (fun y : ℝ => mertensProduct y * log y) atTop
      (𝓝 (exp (-eulerMascheroniConstant))) := by
  sorry

end ArtinPrimitiveRoots
