-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_sHilbertPairing
-- name    : ArtinPrimitiveRoots.exists_cutoff_exists_sHilbertPairing
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T16:34:00.657529+00:00
-- url     : https://prove2.me/theorems/f081c7ca-5f7a-42ac-aee0-4039b028538f
-- title:
--   Lemma 3.2 of OpenAI's Primitive roots paper (proof) — an S-Hilbert pairing for ℓ = 2, 3 that is alternating, makes the S-units Lagrangian, and gives reciprocity at prime generators
-- statement:
--   Let $n > 0$ with $12 \mid n$, let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity (`IsCyclotomicExtension {n} ℚ F`, with `F : Type`), let $\iota : F \to \mathbb C$ be a ring homomorphism, and let $\ell \in \{2, 3\}$. There is $N_0$ such that for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`), with $S$ the set of primes dividing $\mathfrak m$ and $U_S$ the $S$-units, there is a bimultiplicative pairing $H : F^\times \times F^\times \to \mu_\ell(F)$ (`Fˣ →* Fˣ →* rootsOfUnity ℓ F`) with:
--   1. $H(x, x) = 1$ for all $x$ (alternating);
--   2. $H(u, u') = 1$ for all $u, u' \in U_S$ ($U_S$ is isotropic);
--   3. if $H(x, u) = 1$ for every $u \in U_S$, then $x \in U_S\cdot\ker H$, that is, $H(xu^{-1}, \cdot) = 1$ for some $u \in U_S$ ($U_S$ is its own orthogonal modulo the radical);
--   4. $F^\times/\ker H$ is finite;
--   5. for distinct primes $P, P'$ coprime to $\mathfrak m$, and $S$-integers $p, p'$ generating $P$ and $P'$ in the $S$-integers with $H(p, p') = 1$: $\chi_P(p')^{6/\ell} = \chi_{P'}(p)^{6/\ell}$, where $\chi_P$ is the sextic residue symbol (`sexticResidueSymbol ι 𝔪 P`, bundle `Def_ArtinHeckeTheta`).
--
--   Classically $H = \prod_{v \in S}(\cdot, \cdot)_{\ell, v}$, the product of the local $\ell$-th Hilbert symbols at the places of $S$. Clause 1 holds because $-1$ is an $\ell$-th power in $F$, clause 2 by Hilbert reciprocity, clause 3 by the counts (3.1)–(3.2) with the injectivity of $U_S/U_S^\ell$ into $V_\ell$ and local nondegeneracy, clause 4 because the radical consists of the local $\ell$-th powers at $S$, and clause 5 by the product formula with the tame symbols at $P$ and $P'$. Clause 5 states only the case $H(p, p') = 1$, so it does not depend on a sign convention for the Hilbert symbol. It is a cut for `exists_cutoff_nonempty_allowedGen` (Lemma 3.2 and (3.3)).
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 10: “Lemma 3.2 (Generators with fixed power classes). The pairing $H_S$ on $V$ is nondegenerate and alternating. The map $U_S/U_S^6 \to V$ is injective, its image $E$ satisfies $E^\perp = E$, and there is an isotropic subgroup $B$ such that $V = E \oplus B$.” Proof: “For $\ell = 2, 3$, put $V_\ell = F_S^\times/F_S^{\times\ell}$. Local Kummer theory and local reciprocity give a nondegenerate Hilbert pairing on this group [19, Chapter V, Proposition (3.2)].”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 10–11, proof of Lemma 3.2 (the S-Hilbert pairing for ℓ = 2, 3: alternating, U_S isotropic and Lagrangian, finite radical quotient, reciprocity (3.3) at prime generators)

import Mathlib
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain

theorem exists_cutoff_exists_sHilbertPairing :
  ∀ (n : ℕ), 0 < n → 12 ∣ n → ∀ (F : Type) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) (ℓ : ℕ), (ℓ = 2 ∨ ℓ = 3) →
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∃ H : Fˣ →* Fˣ →* rootsOfUnity ℓ F,
        (∀ x, H x x = 1) ∧
        (∀ u ∈ (placesOf 𝔪).unit F, ∀ u' ∈ (placesOf 𝔪).unit F, H u u' = 1) ∧
        (∀ x, (∀ u ∈ (placesOf 𝔪).unit F, H x u = 1) →
          ∃ u ∈ (placesOf 𝔪).unit F, H (x * u⁻¹) = 1) ∧
        Finite (Fˣ ⧸ H.ker) ∧
        ∀ P P' : Ideal (𝓞 F), P.IsPrime → P'.IsPrime → IsExterior 𝔪 P → IsExterior 𝔪 P' →
          P ≠ P' →
          ∀ (p p' : SInt 𝔪) (x x' : Fˣ), (x : F) = p → (x' : F) = p' →
            Ideal.span {p} = P.map (algebraMap (𝓞 F) (SInt 𝔪)) →
            Ideal.span {p'} = P'.map (algebraMap (𝓞 F) (SInt 𝔪)) → H x x' = 1 →
              sexticResidueSymbol ι 𝔪 P p' ^ (6 / ℓ) = sexticResidueSymbol ι 𝔪 P' p ^ (6 / ℓ) := by
  sorry

end ArtinPrimitiveRoots
