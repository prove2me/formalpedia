-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finite_cover_isPullback_inEdgeChart_of_finite
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.exists_finite_cover_isPullback_inEdgeChart_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/b6ba1682-a4ce-581b-a2ca-e1adda50cc47
-- title:
--   Local covering of a Deligne datum by standard edge charts
-- statement:
--   Let $\mathcal O$ be a discrete valuation ring which is a domain with fraction field $K$, let $\pi \in \mathcal O$ be irreducible and assume the residue ring $\mathcal O/(\pi)$ is finite. Let $g \in \mathrm{GL}_2(K)$ be the diagonal matrix $\mathrm{diag}(\pi, 1)$ (entries the images of $\pi$ and $1$ in $K$), let $B$ be a commutative $\mathcal O$-algebra in which the image of $\pi$ is nilpotent, and let $d$ be a Deligne datum over $B$ for $\pi$, i.e. an assignment to every full $\mathcal O$-lattice $M \subseteq K^2$ of a $B$-submodule $\mathrm{line}(M) \subseteq B \otimes_{\mathcal O} M$ with invertible quotient, compatible with inclusions of lattices and with the action of scalar matrices, and satisfying the nondegeneracy condition at every prime of $B$ recorded in `DeligneDatum`. Then there are finitely many elements $f_0, \dots, f_{k-1}$ of $B$ generating the unit ideal and elements $h_0, \dots, h_{k-1}$ of $\mathrm{GL}_2(K)$ such that for each index $i$ and every commutative ring $C$ which is an $\mathcal O$-algebra and a $B$-algebra in a compatible tower and is a localisation of $B$ away from $f_i$, there exists a Deligne datum $d'$ over $C$ which is the pullback along $h_i$ of the base change of $d$ to $C$ (for every full lattice $M$, $d'.\mathrm{line}(M)$ is the preimage of $d_C.\mathrm{line}(h_i \cdot M)$ under the base-changed action of $h_i$), and which satisfies `InEdgeChart` for the pair of lattices $(g \cdot \Lambda_0, \Lambda_0)$, $\Lambda_0$ the standard lattice: at every prime ideal $\mathfrak p$ of $C$ the predicate `EdgeNondegAt` holds for $d'$ with respect to that pair.
--
--   This is the quasi-compactness step in the chart description of the formal upper half-plane underlying Čerednik–Drinfeld uniformisation: the pointwise assertion over local rings (`exists_isPullback_inEdgeChart_of_isLocalRing`) is spread out over a finite cover of $\operatorname{Spec} B$ by basic opens, on each of which a $\mathrm{GL}_2(K)$-translate of the datum lies in the standard edge chart. It feeds the determinant-index refinement and the gluing of the chart data into Mumford's formal scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finite_cover_isPullback_inEdgeChart_of_finite.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_finite_cover_isPullback_inEdgeChart_of_finite
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π) [Finite (𝒪 ⧸ Ideal.span {π})]
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d : DeligneDatum (K := K) π B) :
    ∃ (k : ℕ) (f : Fin k → B) (_ : Ideal.span (Set.range f) = ⊤) (h : Fin k → Matrix.GeneralLinearGroup (Fin 2) K),
      ∀ (i : Fin k) (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] [IsLocalization.Away (f i) C],
        ∃ d' : DeligneDatum (K := K) π C,
          DeligneDatum.IsPullback (K := K) (π := π) C (h i) ((Omega K π).map (IsScalarTower.toAlgHom 𝒪 B C) d) d' ∧
          d'.InEdgeChart π (FullLattice.act g (stdFullLattice K)) (stdFullLattice K) := by sorry
