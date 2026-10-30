-- Prove2me | Theorems.Thm_BartlettBousquetMendelson_LocalRad_proof_thm_3_3_p17_tilde_class_subset
-- name    : BartlettBousquetMendelson.LocalRad.proof_thm_3_3_p17_tilde_class_subset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:01:55.963467+00:00
-- url     : https://prove2.me/theorems/bf254458-2cae-4cc5-9a72-bfee28726472
-- title:
--   Inclusion $\tilde{\mathcal G}_r\subset\{f\in\mathrm{star}(\mathcal F,0):T(f)\le r\}$ (proof of Theorem 3.3, p. 17)
-- statement:
--   Let $\mathcal F$ be a class of functions, $T$ a functional with $T(\alpha f)\le\alpha^2T(f)$ for all $f\in\mathcal F$ and $\alpha\in[0,1]$, and $r>0$. Then
--
--   $$
--   \tilde{\mathcal G}_r=\Big\{\frac{rf}{T(f)\vee r}:f\in\mathcal F\Big\}\subseteq\{g\in\mathrm{star}(\mathcal F,0):T(g)\le r\}.
--   $$
--
--   This inclusion is what lets the hypothesis on $\psi$ over the local star-hull control the Rademacher average of $\tilde{\mathcal G}_r$.
--
--   Differences from the source:
--   - generalization: T : F → ℝ⁺ (as in Theorem 3.3) → T any functional on X → ℝ, no nonnegativity assumed; reason: the inclusion uses only the scaling condition; every nonnegative T of the paper is an instance
--   - encoding: r > 0 from the notation of p. 14 ("λ > 1 and r > 0") → hypothesis 0 < r; reason: G̃_r is defined for r > 0
-- source:
--   Bartlett, Bousquet, Mendelson, Local Rademacher Complexities, Ann. Statist. 33(4) (2005), proof of Theorem 3.3, second part, p. 17 (unnumbered) (IMS electronic reprint, arXiv:math/0508275v1)

import Mathlib
import Definitions.Def_BartlettBousquetMendelson_LocalRad_starHull
import Definitions.Def_BartlettBousquetMendelson_LocalRad_tildeClass

namespace BartlettBousquetMendelson.LocalRad

/-- **`G̃_r` lies in the local star-hull (proof of Theorem 3.3, second part, p. 17; unnumbered).**
Bartlett, Bousquet, Mendelson, *Local Rademacher Complexities*, Ann. Statist. 33(4) (2005) (IMS electronic reprint, arXiv:math/0508275v1), proof of Theorem 3.3, second part, p. 17: "One can easily check that
G̃r ⊂ {f ∈ star(F,0) : T(f) ≤ r}".

If `r > 0` and `T(α f) ≤ α² T(f)` for every `f ∈ F` and `α ∈ [0, 1]`, then every
`r f / (T(f) ∨ r)` with `f ∈ F` lies in `star(F, 0)` and has `T`-value at most `r`.

**Formalization Note.** `T` is any functional on `X → ℝ`; only the scaling condition of
Theorem 3.3 part 2 is assumed, on `F` and `α ∈ [0, 1]`. The paper's `T : F → ℝ⁺` (nonnegativity)
is not needed for this inclusion and is not assumed. -/
theorem proof_thm_3_3_p17_tilde_class_subset {X : Type*} (F : Set (X → ℝ))
    (T : (X → ℝ) → ℝ) (r : ℝ) (hr : 0 < r)
    (hTscale : ∀ f ∈ F, ∀ α ∈ Set.Icc (0 : ℝ) 1, T (α • f) ≤ α ^ 2 * T f) :
    tildeClass F T r ⊆ {g | g ∈ starHull F 0 ∧ T g ≤ r} := by sorry

end BartlettBousquetMendelson.LocalRad
