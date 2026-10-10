-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_differentiable_dedekindZeta_eq_mul_of_isGalois
-- name    : ArtinPrimitiveRoots.exists_differentiable_dedekindZeta_eq_mul_of_isGalois
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T07:12:32.637984+00:00
-- url     : https://prove2.me/theorems/bcaac77f-4016-4028-83ac-a8b06cede0c5
-- title:
--   Aramata–Brauer theorem — for a Galois extension L/K of number fields, ζ_L = ζ_K · h with h entire
-- statement:
--   Let $K$ and $L$ be number fields, with $L$ a $K$-algebra that is Galois over $K$ (`IsGalois K L`). Then there is an entire function $h$ (`Differentiable ℂ h`) with
--
--   $$\zeta_L(s) = \zeta_K(s)\,h(s)\qquad(\operatorname{Re} s > 1),$$
--
--   where $\zeta_K$ and $\zeta_L$ are Mathlib's Dedekind zeta functions (`NumberField.dedekindZeta`, the $L$-series of the number of integral ideals of each norm). Since $\zeta_K$ has no zeros in $\operatorname{Re} s > 1$, $h = \zeta_L/\zeta_K$ there, so the statement says that this quotient continues to an entire function.
--
--   A cut for `kummer_zero_free_of_hecke` (the descent (9.2) in the proof of Lemma 9.1 of OpenAI's *Primitive roots for every admissible integer base*, p. 61). Our proof applies it to $K = \mathbb Q(\mu_q, a^{1/q})$ inside $\widetilde K = K(\mu_{12q})$, in place of the paper's factorization (9.4) of $\zeta_{\widetilde K}/\zeta_K$ into Hecke $L$-functions of $K$, so that no Hecke characters of $K$ are needed; $K$ is real when $q = 2$ and $a > 0$.
--
--   R. Brauer, *On the zeta-functions of algebraic number fields*, Amer. J. Math. 69 (1947), 243–250, [doi:10.2307/2371849](https://doi.org/10.2307/2371849); first proved by H. Aramata, *Über die Teilbarkeit der Dedekindschen Zetafunktionen*, Proc. Imp. Acad. 9 (1933), [doi:10.3792/pia/1195580866](https://doi.org/10.3792/pia/1195580866).
-- source:
--   R. Brauer, On the zeta-functions of algebraic number fields, Amer. J. Math. 69 (1947), https://doi.org/10.2307/2371849, p. 243–250, the Aramata–Brauer theorem (ζ_L/ζ_K is entire for a Galois extension L/K; first proved by H. Aramata, Proc. Imp. Acad. 9 (1933), https://doi.org/10.3792/pia/1195580866)

import Mathlib

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_differentiable_dedekindZeta_eq_mul_of_isGalois (K L : Type) [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧
      ∀ s : ℂ, 1 < s.re → dedekindZeta L s = dedekindZeta K s * h s := by
  sorry

end ArtinPrimitiveRoots
