-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_nonempty_allowedGen
-- name    : ArtinPrimitiveRoots.exists_cutoff_nonempty_allowedGen
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T12:59:15.604379+00:00
-- url     : https://prove2.me/theorems/1c4e753c-6f86-47b6-92b5-24c604508685
-- title:
--   Lemma 3.2 of OpenAI's Primitive roots paper — allowed generators exist once S contains the small primes
-- statement:
--   Let $F$ be a number field generated over $\mathbb Q$ by the $n$-th roots of unity, with $n > 0$ and $12 \mid n$ (`IsCyclotomicExtension {n} ℚ F`), and let $\iota : F \to \mathbb C$ be a ring homomorphism. There is $N_0$ such that for every nonzero ideal $\mathfrak m$ of $\mathcal O_F$ divisible by every nonzero prime ideal of norm at most $N_0$ (`SmallPrimesDvd N₀ 𝔪`) there is a system of allowed generators `AllowedGen ι 𝔪`: a function `gen` from ideals of $\mathcal O_F$ to the ring $R$ of $S$-integers such that, for all ideals $I, J$ coprime to $\mathfrak m$ and nonzero, `gen I` generates $IR$, `gen (I * J)` equals $\varepsilon^6\,$`gen I`$\,$`gen J` for some $S$-unit $\varepsilon$, and for distinct such prime ideals $P, P'$ the sextic residue symbols satisfy $\chi_P(\texttt{gen } P') = \chi_{P'}(\texttt{gen } P)$.
--
--   Here $S$ is the complex places together with the primes dividing $\mathfrak m$. The bound $N_0$ makes $S$ contain the places above $6$ and a set of primes generating the class group, as the paper arranges on p. 8; then $R$ is a principal ideal domain. The bundle note of `Def_ArtinHeckeTheta` explains why these three properties are the paper's notion of allowed generator.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 10, Lemma 3.2: “The pairing $H_S$ on $\mathcal V$ is nondegenerate and alternating. The map $U_S/U_S^6 \to \mathcal V$ is injective, its image $E$ satisfies $E^\perp = E$, and there is an isotropic subgroup $B$ such that $\mathcal V = E \oplus B$. Every exterior fractional ideal $\mathfrak a$ has a generator $a$ whose class $[a]$ in $\mathcal V$ belongs to $B$. Any two such generators differ by an element of $U_S^6$.” and p. 11: “For distinct exterior primes with allowed generators $p, p'$, global reciprocity gives the exact equality $\chi_{\mathfrak p}(p') = \chi_{\mathfrak p'}(p)$. (3.3)”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 10–11, Lemma 3.2 and (3.3) (allowed generators)

import Mathlib
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_nonempty_allowedGen (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → Nonempty (AllowedGen ι 𝔪) := by
  sorry

end ArtinPrimitiveRoots
