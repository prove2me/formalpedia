-- Prove2me | Theorems.Thm_FDivToolkit_lemma_2
-- name    : FDivToolkit.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:19.761628+00:00
-- url     : https://prove2.me/theorems/52fc9d59-e64c-4792-9b58-92a6d6958060
-- title:
--   Lemma 2 — a sufficient condition for (5), inherited by lighter tails
-- statement:
--   Let $H$ be a generating function and $\nu$ a reference model with density $f$.
--
--   1. Condition (7) implies condition (5).
--   2. Let $\hat\nu$ be a second reference model, with density $\hat f$. If $\nu$ satisfies (7) and
--   $$
--   \limsup_{|x|\to\infty}\frac{\hat f(x)}{f(x)}<\infty, \tag{8}
--   $$
--   then $\hat\nu$ satisfies (7) as well.
--
--   Part 1 replaces an integral condition by a tail condition, and part 2 shows that it passes to all more light-tailed reference models.
--
--   Differences from the source:
--   - generalization: lim sup_{|x|→∞} f̂(x)/f(x) < ∞ (8) → ∃ C, eventually for |x| → ∞, f̂ x ≤ C f x; reason: no quotient is formed; the Lean hypothesis also admits tails where f = f̂ = 0, where the paper's quotient is 0/0, and it follows from (8) wherever (8) makes sense
--   - encoding: |x| → ∞, the pair of limits x → ∞ and x → −∞ (footnote 8), with lim sup < ∞ → the filter cocompact ℝ, with an eventual bound by a constant; reason: cocompact ℝ is exactly that pair of limits, and a lim sup of a function is finite exactly when the function is eventually bounded
--   - encoding: distributions ν, η on 𝓢 with densities f, g → functions f, g : ℝ → ℝ with IsRefModel f and IsDensity g, the distributions being densityMeasure f and densityMeasure g, and integrals over 𝓢 written over ℝ where f or g vanishes off 𝓢; reason: the paper uses its distributions only through their densities; measurability is the standing convention of the field, and f = 0 off 𝓢 by footnote 2
-- source:
--   Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), Lemma 2, p.9

import Definitions.Def_FDivToolkit_IsRefModel
import Definitions.Def_FDivToolkit_Cond5
import Definitions.Def_FDivToolkit_Cond7

open Filter

namespace FDivToolkit

/-- Lemma 2, Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), p.9. (i) Condition (7) is
sufficient for condition (5). (ii) If `f` satisfies (7) and a second reference model `f̂` satisfies
(8), `lim sup_{|x|→∞} f̂(x)/f(x) < ∞`, then `f̂` satisfies (7) as well.

**Formalization Note.** (8) is written without a quotient, as `f̂ x ≤ C * f x` eventually for
`|x| → ∞`, so Lean's `x / 0 = 0` plays no role. -/
theorem lemma_2 {H f : ℝ → ℝ} (hH : IsAdmissibleH H) (hf : IsRefModel f) :
    (Cond7 H f → Cond5 H f) ∧
    ∀ fhat : ℝ → ℝ, IsRefModel fhat → Cond7 H f →
      (∃ C : ℝ, ∀ᶠ x in cocompact ℝ, fhat x ≤ C * f x) → Cond7 H fhat := by sorry

end FDivToolkit
