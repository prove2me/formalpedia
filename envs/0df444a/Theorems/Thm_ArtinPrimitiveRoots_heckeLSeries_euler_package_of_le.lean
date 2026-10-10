-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_heckeLSeries_euler_package_of_le
-- name    : ArtinPrimitiveRoots.heckeLSeries_euler_package_of_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T10:46:59.250122+00:00
-- url     : https://prove2.me/theorems/019ae22c-6cf2-4a54-8f33-5788f82c12e7
-- title:
--   p. 16 and §8.3 of OpenAI's Primitive roots paper — Euler product facts for L(s, χ) and the change of modulus that removes finitely many Euler factors
-- statement:
--   Let $F$ be a number field, $\mathfrak m'$ a nonzero ideal of $\mathcal O_F$ contained in an ideal $\mathfrak m$ (so $\mathfrak m \mid \mathfrak m'$), and $\chi$ a finite-order Hecke character of $F$ of modulus $\mathfrak m$ (`HeckeChar F 𝔪`). Then:
--
--   1. $|\chi(I)| \le 1$ for every ideal $I$ of $\mathcal O_F$;
--   2. $L(s, \chi) \ne 0$ for $\operatorname{Re} s > 1$ (`χ.LSeries`);
--   3. there is $B$ with $|L(s, \chi)^{-1}| \le B$ for all $s$ with $\operatorname{Re} s \ge 2$;
--   4. there is a Hecke character $\chi'$ of modulus $\mathfrak m'$ that agrees with $\chi$ on every ideal coprime to $\mathfrak m'$, and for $\operatorname{Re} s > 1$
--   $$L(s, \chi) = L(s, \chi')\prod_{\substack{P \mid \mathfrak m',\ P \nmid \mathfrak m}}\bigl(1 - \chi(P)\,\mathrm N P^{-s}\bigr)^{-1},$$
--   the product running over the nonzero prime ideals $P$ with $\mathfrak m' \le P$ and $P + \mathfrak m = \mathcal O_F$.
--
--   These are the Euler-product facts the paper uses around its incomplete $L$-function $L^S(s, \eta)$: absolute convergence and boundedness of the reciprocal to the right of $\operatorname{Re} s = 1$, and the removal of finitely many Euler factors $1 - \eta(\mathfrak p)q_{\mathfrak p}^{-s}$, which vanish only on $\operatorname{Re} s = 0$, when $S$ is enlarged.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 16: “For $\operatorname{Re} s > 1$, write $\zeta_F^S(s) = \sum_{\mathfrak a} q_{\mathfrak a}^{-s}$ for the Dedekind zeta function with its factors at $S$ omitted, and set $L_F^S(s, \eta) = L^S(s, \eta) := \prod_{\mathfrak p \notin S}(1 - \eta(\mathfrak p)q_{\mathfrak p}^{-s})^{-1}$.”; p. 59: “The reciprocal there is in absolute convergence, the correction is holomorphic and bounded, and the Gaussian gives rapid vertical decay.”; and p. 60: “The finite factors removed from $L_F(s, \eta)$ are either one or $1 - \eta(\mathfrak p)q_{\mathfrak p}^{-s}$ with $|\eta(\mathfrak p)| = 1$; their zeros have real part zero. Thus the same zero exclusion holds for the full $L_F(s, \eta)$.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 16, 59–60, proof of Theorem 1.2, §8.3 (Euler product of L^S(s, η); removal of finitely many Euler factors)

import Mathlib
import Definitions.Def_ArtinHecke

namespace ArtinPrimitiveRoots

open NumberField

theorem heckeLSeries_euler_package_of_le (F : Type*) [Field F] [NumberField F] (𝔪 𝔪' : Ideal (𝓞 F))
    (h𝔪' : 𝔪' ≠ ⊥) (hle : 𝔪' ≤ 𝔪) (χ : HeckeChar F 𝔪) :
    (∀ I : Ideal (𝓞 F), ‖χ.toFun I‖ ≤ 1) ∧
    (∀ s : ℂ, 1 < s.re → χ.LSeries s ≠ 0) ∧
    (∃ B : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖(χ.LSeries s)⁻¹‖ ≤ B) ∧
    ∃ χ' : HeckeChar F 𝔪', (∀ I : Ideal (𝓞 F), I ⊔ 𝔪' = ⊤ → χ'.toFun I = χ.toFun I) ∧
      ∀ s : ℂ, 1 < s.re → χ.LSeries s = χ'.LSeries s *
        ∏ᶠ (P : Ideal (𝓞 F)) (_ : P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪' ≤ P ∧ P ⊔ 𝔪 = ⊤),
          (1 - χ.toFun P * (Ideal.absNorm P : ℂ) ^ (-s))⁻¹ := by
  sorry

end ArtinPrimitiveRoots
