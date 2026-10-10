-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_norm_principalMellin_le
-- name    : ArtinPrimitiveRoots.exists_cutoff_norm_principalMellin_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T10:47:07.164092+00:00
-- url     : https://prove2.me/theorems/b9d085ec-eb56-4cbc-af21-27845f5ad23a
-- title:
--   (8.22) of OpenAI's Primitive roots paper — the principal Mellin integral f_η(Z) is O(Z^{7/15 − 1/20000})
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`) and every finite-order Hecke character $\chi$ of modulus $\mathfrak m$, there are $C$ and $Z_0$ with
--   $$\Bigl|\frac{1}{2\pi i}\int_{(2)} Z^{s - 8/15}e^{(s - 5/6)^2}\frac{\mathcal H(s)}{L(s, \chi)}\,ds\Bigr| \le C Z^{7/15 - 1/20000}$$
--   for every real $Z \ge Z_0$. Here $\mathcal H = $ `χ.principalCorrection ι` and the left side is `χ.principalMellin ι Z`.
--
--   The set $S$ of the paper is the complex places together with the primes dividing $\mathfrak m$; $N_0$ depends on $F$ (and $\iota$) only, while $C$ and $Z_0$ may depend on $\mathfrak m$ and $\chi$, as the paper's constants and onsets depend on $F$, $S$ and $\eta$. The bundle note explains how $\mathcal H$ and $L(s, \chi)$ correspond to the paper's $\mathcal H_\eta$ and $L^S(s, \eta)$.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 59: “Use Theorem 7.2 with, for example, a loss $10^{-5}$. Since $1/6000 - 10^{-5} > 1/20000$ and $c_0 \ne 0$, the preceding identity implies the safe bound $f_\eta(Z) \ll_{F,S,\eta,W_0,W_1} Z^{7/15-1/20000}$ ($Z$ sufficiently large). (8.22)” The function $f_\eta$ is defined in (8.13), p. 56.
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 59, (8.22)

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_norm_principalMellin_le (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → ∀ χ : HeckeChar F 𝔪,
      ∃ C Z₀ : ℝ, ∀ Z : ℝ, Z₀ ≤ Z →
        ‖χ.principalMellin ι Z‖ ≤ C * Z ^ ((7 : ℝ) / 15 - 1 / 20000) := by
  sorry

end ArtinPrimitiveRoots
