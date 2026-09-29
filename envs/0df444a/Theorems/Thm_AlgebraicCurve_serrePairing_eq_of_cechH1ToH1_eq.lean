-- Prove2me | Theorems.Thm_AlgebraicCurve_serrePairing_eq_of_cechH1ToH1_eq
-- name    : AlgebraicCurve.serrePairing_eq_of_cechH1ToH1_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/25939fbf-ed1c-5ef3-b3f5-75ab27c96563
-- title:
--   Chart independence of the Serre residue pairing
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, equipped with: a canonical local residue datum `dataKStar` at every place of $F/K$; the assumption that for each place $v$ the element `v.dCoord` spans $\Omega[F\!\restriction\!K]$ over $F$; nontriviality of $\Omega[F\!\restriction\!K]$; `HasCanonicalDivisor`, i.e. every nonzero $\omega \in \Omega[F\!\restriction\!K]$ admits a divisor whose value at each place $v$ is `v.ordDifferential ω`; and `HasPrincipalDivisors`, i.e. every nonzero $f \in F$ admits a divisor of degree $0$ whose value at each $v$ is `v.ord f`. Assume `ResidueTheorem K F`: for every nonzero $\omega$ and every $f \in F$, the Weil differential `weilOfKaehler K F` attached to $\omega$ annihilates the diagonal adele of $f$. Let $S_0, S_1, T_0, T_1$ be sets of places with $S_0 \cup S_1 = T_0 \cup T_1$ the set of all places, and let $\omega$ lie in `regularDifferentials K F`, i.e. at each place $v$ one has $\omega = f \cdot$ `v.dCoord` for some $f$ in the valuation ring of $v$. Let $x$ be a class in $\check H^1(\{S_0,S_1\}, 0)$, the quotient of $\{f : v(f) \le 1 \text{ for all } v \in S_0 \cap S_1\}$ by the image of the Čech difference map, and let $y$ be a class in $\check H^1(\{T_0,T_1\}, 0)$. If $x$ and $y$ have the same image under `cechH1ToH1` in $H^1(0)$, the quotient of the répartitions by `repartitionsOf 0 ⊔ principalRepartitions K F`, then the Serre pairing values $\langle \omega, x\rangle$ and $\langle \omega, y\rangle$ in $K$ coincide.
--
--   The Serre pairing $\langle\omega,[f]\rangle = \sum_{v \notin S_0} \mathrm{Tr}\,\mathrm{res}_v(f\omega)$ is defined relative to a chosen covering pair of sets of places; this result shows that for a regular differential it factors through the répartition cohomology group $H^1(0) = \mathbb{A}/(\mathbb{A}(0)+F)$, so that classes computed from different chart pairs may be compared. It is used when the two coverings come from different sources, for instance the preimages of one covering under the two degeneracy maps of a Hecke correspondence, and supports the comparison of Serre pairings along trace and pullback maps and the Hecke-equivariance computations on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_serrePairing_eq_of_cechH1ToH1_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_SerrePairing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open KaehlerDifferential
namespace AlgebraicCurve

theorem serrePairing_eq_of_cechH1ToH1_eq {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]
    [HasCanonicalLocalResidueKStar K F] [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    [HasCanonicalDivisor (K := K) (F := F)] [HasPrincipalDivisors K F]
    (hRT : ResidueTheorem K F) {S₀ S₁ T₀ T₁ : Set (Place K F)}
    (hS : S₀ ∪ S₁ = Set.univ) (hT : T₀ ∪ T₁ = Set.univ)
    (ω : ↥(regularDifferentials K F)) (x : cechH1 S₀ S₁ (0 : Divisor K F)) (y : cechH1 T₀ T₁ (0 : Divisor K F))
    (h : cechH1ToH1 hS 0 x = cechH1ToH1 hT 0 y) :
    serrePairing hRT hS ω x = serrePairing hRT hT ω y := by sorry
