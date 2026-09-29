-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_deligneDatum_away_forall_map
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_deligneDatum_away_forall_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/5f8b837c-e181-5bea-a7b1-03c34db6f82f
-- title:
--   A Drinfeld datum is locally given by a Deligne datum
-- statement:
--   Let $\mathcal O$ be a discrete valuation ring which is a domain, $K$ a field that is an $\mathcal O$-algebra and a fraction field of $\mathcal O$, and $\pi \in \mathcal O$ irreducible. Let $B$ be a commutative $\mathcal O$-algebra in which the image of $\pi$ is nilpotent, let $Q$ be a `DrinfeldDatum` for $\pi$ over $B$ — so in particular full lattices $N_0(y) \le N_1(y)$ in $K^2$ for each $y \in \operatorname{Spec} B$, packaged as full lattices `Q.L₀ y`, `Q.L₁ y`, with $\pi N_1(y) \subseteq N_0(y)$, open membership loci, invertible $B$-modules $T_0, T_1$ linked by $\Pi_0, \Pi_1$ composing to $\pi$, and maps $u_i(y)$ from the base change $B_y \otimes_{\mathcal O} N_i(y)$ to the stalk of $T_i$ at $y$ — and let $x$ be a prime of $B$. The assertion is that there is $r \in B$ with $r \notin x$ and a `DeligneDatum` $d$ for $\pi$ over $B[1/r]$, i.e. an assignment $M \mapsto d.\mathrm{line}\,M \subseteq B[1/r] \otimes_{\mathcal O} M$ on full lattices $M$ of $K^2$ with invertible quotients, compatible with inclusions and with scalar homotheties, and nondegenerate at every prime, such that for every prime $y$ with $r \notin y$ and every $\mathcal O$-algebra map $g : B[1/r] \to B_y$ into the localisation of $B$ at $y$ satisfying $g(b/1) = b/1$ for all $b \in B$, the base change $d.\mathrm{map}\,\pi\,g$ (whose lines are the $B_y$-spans of the images of the lines of $d$ under $g \otimes \mathrm{id}$) satisfies $\ker u_0(y) = (d.\mathrm{map}\,\pi\,g).\mathrm{line}\,(\mathrm{L}_0\,y)$, $\ker u_1(y) = (d.\mathrm{map}\,\pi\,g).\mathrm{line}\,(\mathrm{L}_1\,y)$, and `InEdgeChart` for the pair $(\mathrm{L}_0\,y, \mathrm{L}_1\,y)$: for every prime $\mathfrak p$ of $B_y$ one has $N_0(y) \subseteq N_1(y)$, $\pi N_1(y) \subseteq N_0(y)$, every $v \in N_1(y)\setminus N_0(y)$ has $1 \otimes v \notin \mathrm{line}\,(\mathrm{L}_1\,y) + \mathfrak p\cdot\top$, and every $v' \in N_0(y)$ not of the form $\pi w$ with $w \in N_1(y)$ has $1 \otimes v' \notin \mathrm{line}\,(\mathrm{L}_0\,y) + \mathfrak p\cdot\top$.
--
--   This is the local form of the comparison between Drinfeld's moduli description and Deligne's description of the formal upper half plane: on a basic open neighbourhood $D(r)$ of a given point, the Drinfeld datum is recovered from a single Deligne datum over $B[1/r]$, lying in the edge chart attached to the simplex $(N_0, N_1)$ at each point, and compatibly with passage to the local rings. It is used to produce a finitely generated open cover carrying such data, via [`CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_fg_forall_lineBaseChange_eq`](thm.html#CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_fg_forall_lineBaseChange_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_deligneDatum_away_forall_map.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_deligneDatum_away_forall_map
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) :
    ∃ r : B, r ∉ x.asIdeal ∧ ∃ d : DeligneDatum (K := K) π (Localization.Away r),
      ∀ (y : PrimeSpectrum B), r ∉ y.asIdeal →
        ∀ g : Localization.Away r →ₐ[𝒪] locRing B y,
          (∀ b : B, g (algebraMap B (Localization.Away r) b) = algebraMap B (locRing B y) b) →
          LinearMap.ker (Q.u₀ y) = (d.map π g).line (Q.L₀ y) ∧ LinearMap.ker (Q.u₁ y) = (d.map π g).line (Q.L₁ y) ∧
            (d.map π g).InEdgeChart π (Q.L₀ y) (Q.L₁ y) := by sorry
