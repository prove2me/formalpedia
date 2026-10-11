-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_gaussPhase_mul_gaussPhase_mul_conj_gaussLambda_mul_conj_gaussG_eq_neg_one
-- name    : ArtinPrimitiveRoots.exists_cutoff_gaussPhase_mul_gaussPhase_mul_conj_gaussLambda_mul_conj_gaussG_eq_neg_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T16:06:07.953985+00:00
-- url     : https://prove2.me/theorems/3a78a688-40be-40be-abe1-744aa5711f7b
-- title:
--   Davenport–Hasse for m = 2, as (3.9) of OpenAI's Primitive roots paper — γ₁(𝔭)γ₂(𝔭) conj Λ(𝔭) conj G(𝔭) = −1
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that the following holds for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`) and every system of allowed generators $g$ (`AllowedGen ι 𝔪`): for every prime $P$ coprime to $\mathfrak m$ (`IsExterior 𝔪 P`),
--   $$\gamma_1(P)\,\gamma_2(P)\,\overline{\Lambda(P)}\,\overline{G(P)} = -1,$$
--   with $\gamma_j$ = `gaussPhase g j`, $\Lambda$ = `gaussLambda ι` and $G$ = `gaussG g` (bundle `Def_ArtinHeckeTheta`).
--
--   Since $|\Lambda(P)| = |G(P)| = 1$, this is the third identity of (3.9), $\gamma_1\gamma_2 = -\Lambda G$. The paper derives it from the duplication case $m = 2$ of the Davenport–Hasse product formula, $J(\chi, \chi) = \chi(4) J(\chi^3, \chi)$, equivalently $G_1 G_4 = \chi(4) G_2 G_3$ (p. 15). It was checked numerically in $\mathbb Q(\zeta_{12})$ at primes of norms $13, 37, 61$. It gives $\gamma_1\gamma_2\vartheta = -\eta$ (p. 49) and is a cut for `exists_cutoff_freqCoeff_principalFreq_eq_one_and_eq_mul`.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 13, Lemma 3.4: “There are a unitary Hecke character $\Lambda$, unramified outside $S$, and a finite-order Hecke character $G$, unramified outside $S$, such that for every exterior prime $\mathfrak p$, $\gamma_2(\mathfrak p)^3 = -\Lambda(\mathfrak p)$, $G(\mathfrak p) = \overline{\chi_{\mathfrak p}(4)}\,\gamma_3(\mathfrak p)$, $\gamma_1(\mathfrak p)\gamma_2(\mathfrak p) = -\Lambda(\mathfrak p)G(\mathfrak p)$. (3.9)” The classical source of the product formula is H. Davenport and H. Hasse, *Die Nullstellen der Kongruenzzetafunktionen in gewissen zyklischen Fällen*, J. Reine Angew. Math. 172 (1935), 151–182, https://doi.org/10.1515/crll.1935.172.151.
-- source:
--   H. Davenport and H. Hasse, Die Nullstellen der Kongruenzzetafunktionen in gewissen zyklischen Fällen, J. Reine Angew. Math. 172 (1935), 151–182, https://doi.org/10.1515/crll.1935.172.151, p. 151–182, the Davenport–Hasse product formula, case m = 2 (cited for Lemma 3.4, (3.9), of OpenAI, Primitive roots for every admissible integer base, pp. 13, 15)

import Mathlib
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_gaussPhase_mul_gaussPhase_mul_conj_gaussLambda_mul_conj_gaussG_eq_neg_one
    (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → ∀ g : AllowedGen ι 𝔪,
      ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P →
        gaussPhase g 1 P * gaussPhase g 2 P * starRingEnd ℂ (gaussLambda ι P) *
          starRingEnd ℂ (gaussG g P) = -1 := by
  sorry

end ArtinPrimitiveRoots
