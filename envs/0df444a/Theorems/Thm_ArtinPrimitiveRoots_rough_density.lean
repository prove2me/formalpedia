-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_rough_density
-- name    : ArtinPrimitiveRoots.rough_density
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T09:27:18.468828+00:00
-- url     : https://prove2.me/theorems/82cb2258-18c3-48cd-a410-8b6328b91c12
-- title:
--   Lemma 11.2 (OpenAI) — the rough-number density identity and upper bound
-- statement:
--   With $D_\gamma(w) = $ `roughDensity γ w`:
--
--   1. for every real $0 < b < 1/2$, $\displaystyle\int_b^{1/2} D_t(1 - t)\,\frac{dt}{t} = D_b(1) - 1$;
--   2. there are $b_0 > 0$ and $C_d > 0$ such that for every $0 < b < b_0$,
--   $$D_b(1) \le \frac{\exp(-\gamma_E)}{b}\bigl(1 + C_d\exp(-\tfrac{1/20}{b})\bigr),$$
--   where $\gamma_E$ is Euler's constant (`Real.eulerMascheroniConstant`).
--
--   **Formalization note.** The integral is an interval integral, so its value at the single point $t = 1/2$ is irrelevant and the paper's left-limit convention there needs no encoding. The bound is stated with $c_d = 1/20$, which the paper says one may take.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 72: “Lemma 11.2 (Rough-number density). For $0 < b < 1/2$, $\int_b^{1/2} D_t(1 - t)\,\frac{dt}{t} = D_b(1) - 1$, (11.6) where the integrand at $1/2$ is interpreted by its left limit. There are absolute constants $b_0, c_d, C_d > 0$ such that, for $0 < b < b_0$, $D_b(1) \le \frac{\exp(-\gamma_E)}{b}\bigl(1 + C_d\exp(-c_d/b)\bigr)$. (11.7) One may take $c_d = 1/20$.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 72, Lemma 11.2

import Mathlib
import Definitions.Def_ArtinSieve

namespace ArtinPrimitiveRoots

open Real

theorem rough_density :
    (∀ b : ℝ, 0 < b → b < 1 / 2 →
      ∫ t in b..(1 / 2), roughDensity t (1 - t) / t = roughDensity b 1 - 1) ∧
    ∃ b₀ C_d : ℝ, 0 < b₀ ∧ 0 < C_d ∧ ∀ b : ℝ, 0 < b → b < b₀ →
      roughDensity b 1 ≤
        exp (-eulerMascheroniConstant) / b * (1 + C_d * exp (-(1 / 20) / b)) := by
  sorry

end ArtinPrimitiveRoots
