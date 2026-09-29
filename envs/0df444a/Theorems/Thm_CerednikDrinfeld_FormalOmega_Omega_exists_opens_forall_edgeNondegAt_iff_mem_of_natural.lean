-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_exists_opens_forall_edgeNondegAt_iff_mem_of_natural
-- name    : CerednikDrinfeld.FormalOmega.Omega.exists_opens_forall_edgeNondegAt_iff_mem_of_natural
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/5ba158e8-d382-505e-ad44-f0bc2b7f5fef
-- title:
--   Edge non-degeneracy of a natural family cuts out an open set
-- statement:
--   Let $\mathcal O$ be a discrete valuation ring (a domain) with fraction field $K_0$, let $\pi\in\mathcal O$ be irreducible, and suppose the residue ring $\mathcal O/(\pi)$ is finite, of cardinality $q$. Let $C$ be a Noetherian $\mathcal O$-algebra in which the image of $\pi$ is nilpotent, and let $f_X\colon X\to\operatorname{Spec} C$ be a morphism of schemes locally of finite type. Suppose given, for every Noetherian $C$-algebra $S$ that is also an $\mathcal O$-algebra compatibly with $C$, a map $\theta_S$ from the set of $C$-morphisms $\operatorname{Spec} S\to X$ over $\operatorname{Spec} C$ to the set of Deligne data $\mathrm{DeligneDatum}\,\pi\,S$ for $K_0$ over $S$ (a family of $S$-lines in $S\otimes_{\mathcal O}M$, one for each full lattice $M\subset K_0^2$, with invertible quotients, monotone and homothety-equivariant, non-degenerate at every prime), and assume $\theta$ is natural: for every $C$-algebra map $g\colon S\to S'$, $\theta_{S'}$ of the composite point equals the base change along $g$ (as an $\mathcal O$-algebra map) of $\theta_S(x)$. Let finally $M'\le M$ be full lattices in $K_0^2$ with $\pi M\subseteq M'$. Then there is an open subset $U\subseteq X$ such that for every such $S$, every point $x\colon\operatorname{Spec} S\to X$ over $C$ and every prime ideal $\mathfrak q\subset S$, the datum $\theta_S(x)$ is edge-non-degenerate at $\mathfrak q$ for the pair $(M',M)$ — that is, $M'\le M$, $\pi M\subseteq M'$, and for $v\in M\setminus M'$ one has $1\otimes v\notin \mathrm{line}(M)+\mathfrak q\,(S\otimes_{\mathcal O}M)$, while for $v'\in M'$ not of the form $\pi w$ with $w\in M$ one has $1\otimes v'\notin \mathrm{line}(M')+\mathfrak q\,(S\otimes_{\mathcal O}M')$ — if and only if the image of $\mathfrak q$ under $x$ lies in $U$.
--
--   This is the Zariski-openness step underlying the edge charts of the formal model $\widehat\Omega$ in the Čerednik–Drinfeld uniformisation: a condition on Deligne data which is open on each affine and stable under base change defines an open subscheme of any scheme carrying a natural family of such data. It is used in the construction of open immersions of stratum windows for families of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_Omega_exists_opens_forall_edgeNondegAt_iff_mem_of_natural.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.Omega.exists_opens_forall_edgeNondegAt_iff_mem_of_natural

    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) [Finite (𝒪 ⧸ Ideal.span {π})]

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π))
    (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of C)) [LocallyOfFiniteType fX]

    (θ : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
      (Scheme.nilpPoints fX).obj S → (Omega K₀ π).obj S)
    (hnat : ∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      [CommRing S'] [Algebra C S'] [IsNoetherianRing S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S']
      (g : S →ₐ[C] S') (x : (Scheme.nilpPoints fX).obj S),
      θ S' ((Scheme.nilpPoints fX).map g x) = (Omega K₀ π).map (g.restrictScalars 𝒪) (θ S x))

    (M' M : FullLattice 𝒪 K₀) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K₀ π • v ∈ M'.1) :
    ∃ U : X.Opens,
      ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
        (x : (Scheme.nilpPoints fX).obj S) (𝔮 : Ideal S) (h𝔮 : 𝔮.IsPrime),
        DeligneDatum.EdgeNondegAt π (θ S x) 𝔮 M' M ↔ x.1.base ⟨𝔮, h𝔮⟩ ∈ U := by sorry
