-- Prove2me | Theorems.Thm_Algebra_PatchingDatum_nonempty_patchingLevel_bot
-- name    : Algebra.PatchingDatum.nonempty_patchingLevel_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/9ce1b638-b77e-55da-ba61-0f902e08f27d
-- title:
--   Taylor–Wiles patching: a patched level with zero relation ideal
-- statement:
--   Let $\mathcal O$ be a domain that is a discrete valuation ring, complete with respect to its maximal ideal $\mathfrak m$ and with finite residue field, let $\ell, r$ be natural numbers with $\ell \in \mathfrak m$, let $R$ be a commutative $\mathcal O$-algebra and let $M$ be an $R$-module. Write $B = \mathcal O[[X_0,\dots,X_{r-1}]]$ for `MvPowerSeries (Fin r) 𝒪`. For an ideal $J \subseteq B$, an inhabitant of the project's structure [`Algebra.PatchingLevel 𝒪 r R M J`](def/Algebra_PatchingDatum.html#L5) consists of: a $B$-module $N$; an $\mathcal O$-algebra endomorphism $\varphi$ of $B$; a surjective $\mathcal O$-algebra map $\psi : B \to R$ with $\psi(\varphi(X_i)) = 0$ for all $i$; a surjective additive map $\pi : N \to M$ satisfying $\pi(f \cdot x) = \psi(f)\,\pi(x)$ and whose kernel is exactly $(\varphi(X_0),\dots,\varphi(X_{r-1}))\,N$; and a natural number $d$ together with $b_0,\dots,b_{d-1} \in N$ such that every $x \in N$ can be written $x = \sum_i \varphi(c_i)\,b_i$ with $c_i \in B$, and such that $\sum_i \varphi(c_i)\,b_i = 0$ if and only if every $c_i$ lies in $J$. A patching datum [`Algebra.PatchingDatum 𝒪 ℓ r R M`](def/Algebra_PatchingDatum.html#L39) is a family, indexed by $n \in \mathbb N$, of patching levels for the ideals $J_n = ((1+X_0)^{\ell^n}-1,\dots,(1+X_{r-1})^{\ell^n}-1)$. The theorem asserts that from such a datum the type [`Algebra.PatchingLevel 𝒪 r R M ⊥`](def/Algebra_PatchingDatum.html#L5) is nonempty: there is a patching level whose relation ideal is the zero ideal, so that the $b_i$ form a basis of $N$ over $B$ acting through $\varphi$.
--
--   This is the abstract patching step of the Taylor–Wiles method in the formulation of Diamond and Fujiwara: a compatible system of level-$n$ patching data is assembled into a single datum over the full power series ring. Unlike the textbook statement, nothing here refers to Taylor–Wiles primes, Selmer groups, deformation rings or Hecke modules; the hypotheses $\ell \in \mathfrak m$ and the finiteness of the residue field are the only arithmetic input, and the content is pure commutative algebra about the project's structures [`Algebra.PatchingDatum`](def/Algebra_PatchingDatum.html#L39) and [`Algebra.PatchingLevel`](def/Algebra_PatchingDatum.html#L5). It feeds [`Algebra.PatchingDatum.bijective_and_free_of_surjective`](thm.html#Algebra.PatchingDatum.bijective_and_free_of_surjective), which deduces that a surjection $R \to T$ of $\mathcal O$-algebras acting compatibly on $M$ is an isomorphism with $M$ free, and through it [`WeierstrassCurve.isModularModelOfLevel_of_patchingDatum`](thm.html#WeierstrassCurve.isModularModelOfLevel_of_patchingDatum), the passage from a patching datum to modularity of an explicit level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_PatchingDatum_nonempty_patchingLevel_bot.lean

import Definitions.Def_Algebra_PatchingDatum
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Algebra.PatchingDatum.nonempty_patchingLevel_bot
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    {ℓ r : ℕ} (hℓ : (ℓ : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    {R : Type} [CommRing R] [Algebra 𝒪 R] {M : Type} [AddCommGroup M] [Module R M]
    (P : Algebra.PatchingDatum 𝒪 ℓ r R M) :
    Nonempty (Algebra.PatchingLevel 𝒪 r R M ⊥) := by sorry
