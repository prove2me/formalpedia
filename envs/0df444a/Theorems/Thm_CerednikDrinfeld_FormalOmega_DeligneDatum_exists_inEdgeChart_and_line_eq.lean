-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_inEdgeChart_and_line_eq
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.exists_inEdgeChart_and_line_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/1360af41-3ebb-53b9-8e26-042dd28a10ba
-- title:
--   Edge diagrams extend to Deligne data on widehatΩ
-- statement:
--   Let $\mathcal{O}$ be a discrete valuation ring (a commutative domain), $K$ its fraction field, $\pi \in \mathcal{O}$ irreducible, and $B$ a commutative $\mathcal{O}$-algebra. Let $M' , M$ be full lattices in $K^2$, i.e. finitely generated $\mathcal{O}$-submodules of $\mathrm{Fin}\,2 \to K$ whose $K$-span is everything, with $M' \subseteq M$ and $\pi M \subseteq M'$. Let $N \subseteq B \otimes_{\mathcal{O}} M$ and $N' \subseteq B \otimes_{\mathcal{O}} M'$ be $B$-submodules whose quotients $(B \otimes_{\mathcal{O}} M)/N$ and $(B \otimes_{\mathcal{O}} M')/N'$ are invertible $B$-modules, and assume: the base change of the inclusion $M' \hookrightarrow M$ carries $N'$ into $N$; the base change of multiplication by $\pi$, viewed as a map $M \to M'$, carries $N$ into $N'$; for every prime ideal $\mathfrak{p}$ of $B$ and every $v \in M \setminus M'$ one has $1 \otimes v \notin N + \mathfrak{p}\,(B \otimes_{\mathcal{O}} M)$; and for every prime $\mathfrak{p}$ and every $v' \in M'$ not of the form $\pi w$ with $w \in M$ one has $1 \otimes v' \notin N' + \mathfrak{p}\,(B \otimes_{\mathcal{O}} M')$. Then there is a Deligne datum $d$ over $B$ for $\pi$ — a choice of $B$-submodule $d.\mathrm{line}\,L \subseteq B \otimes_{\mathcal{O}} L$ with invertible quotient for every full lattice $L$, monotone under inclusions of lattices, compatible with the action of scalar homotheties $\mathrm{scalarGL}(c)$, $c \in K^{\times}$, and satisfying the above two non-containment conditions at some nested pair of lattices for each prime of $B$ — such that $d.\mathrm{line}\,M = N$, $d.\mathrm{line}\,M' = N'$, and $d$ satisfies `InEdgeChart` for $(M', M)$, i.e. for every prime $\mathfrak{p}$ of $B$ the pair $(M', M)$ itself realises the non-containment conditions for $d$.
--
--   This is the existence half of the statement that the edge charts cover Drinfeld's formal upper half plane: an edge diagram over an arbitrary base $B$, attached to a nested pair of lattices $\pi M \subseteq M' \subseteq M$, is the restriction of a point of $\widehat{\Omega}$ lying in the corresponding edge chart (Boutot–Carayol I, Prop. 4.4). It is used to produce Deligne data from local data, both in the nilpotent case and in the construction of Deligne data away from a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_inEdgeChart_and_line_eq.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_inEdgeChart_and_line_eq
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    {M' M : FullLattice 𝒪 K} (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (N : Submodule B (latticeBaseChange 𝒪 K B M)) (N' : Submodule B (latticeBaseChange 𝒪 K B M'))
    [Module.Invertible B (latticeBaseChange 𝒪 K B M ⧸ N)] [Module.Invertible B (latticeBaseChange 𝒪 K B M' ⧸ N')]
    (hmono : N'.map (inclBaseChange B hle) ≤ N)
    (hsmul : N.map ((smulInto π hπM).baseChange B :
      latticeBaseChange 𝒪 K B M →ₗ[B] latticeBaseChange 𝒪 K B M') ≤ N')
    (h₁ : ∀ 𝔭 : Ideal B, 𝔭.IsPrime → ∀ v : ↥M.1, (v : Fin 2 → K) ∉ M'.1 →
      (1 : B) ⊗ₜ[𝒪] v ∉ N ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)))
    (h₂ : ∀ 𝔭 : Ideal B, 𝔭.IsPrime → ∀ v' : ↥M'.1,
      (¬ ∃ w : ↥M.1, (v' : Fin 2 → K) = algebraMap 𝒪 K π • (w : Fin 2 → K)) →
      (1 : B) ⊗ₜ[𝒪] v' ∉ N' ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M'))) :
    ∃ d : DeligneDatum (K := K) π B, d.line M = N ∧ d.line M' = N' ∧ d.InEdgeChart π M' M := by sorry
