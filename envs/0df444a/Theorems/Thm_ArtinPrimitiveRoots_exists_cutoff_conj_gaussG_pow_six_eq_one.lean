-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_conj_gaussG_pow_six_eq_one
-- name    : ArtinPrimitiveRoots.exists_cutoff_conj_gaussG_pow_six_eq_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T16:07:11.089173+00:00
-- url     : https://prove2.me/theorems/041330bd-93ea-42af-ba23-dd777c5c5b9d
-- title:
--   Lemma 3.4 of OpenAI's Primitive roots paper — the correction character G has sixth power 1 at exterior primes (γ₃(𝔭) is a sign)
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`) and every system of allowed generators $g$ (`AllowedGen ι 𝔪`): for every prime $P$ coprime to $\mathfrak m$ (`IsExterior 𝔪 P`), $\overline{G(P)}^{\,6} = 1$, with $G$ = `gaussG g` (bundle `Def_ArtinHeckeTheta`).
--
--   Here $G(P) = \overline{\chi_P(4)}\,\gamma_3(P)$ with $\chi_P(4)$ a sixth root of unity and $\gamma_3(P)$ a sign. It was checked numerically in $\mathbb Q(\zeta_{12})$ at primes of norms $13, 37, 61$. It gives $\vartheta(\mathfrak p)^6 = \overline{\Lambda(\mathfrak p)^6}\,\eta(\mathfrak p)^6$, the value $\theta$ of the table (7.17), and is a cut for `exists_cutoff_freqCoeff_principalFreq_eq_one_and_eq_mul`.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 13, Lemma 3.4: “$G(\mathfrak p) = \overline{\chi_{\mathfrak p}(4)}\,\gamma_3(\mathfrak p)$ […] The values $\gamma_3(\mathfrak p)$ are signs”; p. 15: “equivalently Gauss inversion gives $\gamma_3(\mathfrak p)^2 = \chi_{\mathfrak p}(-1)^3 = 1$.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 13, 15, Lemma 3.4 and its proof (G(𝔭) = conj χ_𝔭(4) γ₃(𝔭) with γ₃(𝔭) a sign)

import Mathlib
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_conj_gaussG_pow_six_eq_one (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → ∀ g : AllowedGen ι 𝔪,
      ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → starRingEnd ℂ (gaussG g P) ^ 6 = 1 := by
  sorry

end ArtinPrimitiveRoots
