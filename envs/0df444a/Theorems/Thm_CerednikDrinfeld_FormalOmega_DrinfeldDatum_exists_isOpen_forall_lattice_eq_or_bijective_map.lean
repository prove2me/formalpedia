-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isOpen_forall_lattice_eq_or_bijective_map
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isOpen_forall_lattice_eq_or_bijective_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/e8b942e5-0695-58ea-be01-eb0a46b0e959
-- title:
--   Three local types of lattice pairs near a point of a Drinfeld datum
-- statement:
--   Let $\mathcal{O}$ be a discrete valuation ring that is a domain, with field of fractions $K$ (an $\mathcal{O}$-algebra which is the fraction ring of $\mathcal{O}$), and let $\pi \in \mathcal{O}$ be irreducible. Let $B$ be a commutative $\mathcal{O}$-algebra in which the image of $\pi$ is nilpotent, and let $Q$ be a Drinfeld datum over $B$ for $\pi$ and $K$: thus $Q$ assigns to each point of $\operatorname{Spec} B$ two $\mathcal{O}$-submodules $N_0(y) \le N_1(y)$ of $K^2$, each finitely generated and spanning $K^2$ over $K$, with $\pi \cdot N_1(y) \subseteq N_0(y)$ and with each membership locus $\{y : v \in N_i(y)\}$ open; together with invertible $B$-modules $T_0$, $T_1$ and $B$-linear maps $\Pi_0 : T_0 \to T_1$, $\Pi_1 : T_1 \to T_0$ whose two composites are multiplication by the image of $\pi$, and rigidifying isomorphisms identifying, at each point, the base change of the lattices $N_0, N_1$ to the local ring with the stalks of $T_0, T_1$, compatibly with $\Pi_0$ and with multiplication by $\pi$. Let $x$ be a point of $\operatorname{Spec} B$. The assertion is that there is an open set $U$ containing $x$ such that every $y \in U$ satisfies $N_0(x) \le N_0(y)$ and $N_1(x) \le N_1(y)$, and at least one of the following three alternatives holds: either $N_0(y) = N_0(x)$ and $N_1(y) = N_1(x)$; or the localisation of $\Pi_0$ at the prime of $y$ is bijective and $N_0(y) = N_1(y) = N_1(x)$; or the localisation of $\Pi_1$ at the prime of $y$ is bijective, $N_0(y) = N_0(x)$, and $N_1(y) = \{v \in K^2 : \pi v \in N_0(x)\}$, that is, $N_1(y) = \pi^{-1} N_0(x)$.
--
--   This is the local case analysis for the pair of lattice functions attached to a Drinfeld datum, as in Boutot–Carayol I (5.1)(d) and (5.5): near a given point the pair $(N_0, N_1)$ either stays equal to $(M', M) = (N_0(x), N_1(x))$ or jumps to $(M, M)$ or to $(M', \pi^{-1}M')$, according to which of $\Pi_0$, $\Pi_1$ becomes invertible. It is used in the construction of a Deligne datum away from the degenerate locus, namely by [`CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_deligneDatum_away_forall_map`](thm.html#CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_deligneDatum_away_forall_map).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isOpen_forall_lattice_eq_or_bijective_map.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isOpen_forall_lattice_eq_or_bijective_map
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) :
    ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      Q.N₀ x ≤ Q.N₀ y ∧ Q.N₁ x ≤ Q.N₁ y ∧
      ((Q.N₀ y = Q.N₀ x ∧ Q.N₁ y = Q.N₁ x) ∨
       (Function.Bijective (LocalizedModule.map y.asIdeal.primeCompl Q.Pi₀) ∧
          Q.N₀ y = Q.N₁ x ∧ Q.N₁ y = Q.N₁ x) ∨
       (Function.Bijective (LocalizedModule.map y.asIdeal.primeCompl Q.Pi₁) ∧
          Q.N₀ y = Q.N₀ x ∧ ∀ v : Fin 2 → K, v ∈ Q.N₁ y ↔ algebraMap 𝒪 K π • v ∈ Q.N₀ x)) := by sorry
