-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_nonempty_mumfordGlueCore_of_isSchottky
-- name    : CerednikDrinfeld.FormalOmega.nonempty_mumfordGlueCore_of_isSchottky
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/b5f704af-0835-585c-a91a-82badc5c87d7
-- title:
--   Existence of a Mumford gluing core for a type-preserving Schottky group
-- statement:
--   Let $r$ be a prime, let $\mathcal{O}$ be a domain that is a discrete valuation ring, let $\pi \in \mathcal{O}$ be irreducible, and assume the residue ring $\mathcal{O}/(\pi)$ has exactly $r$ elements; let $K_0$ be a field which is a fraction field of $\mathcal{O}$, and let $g_1 \in \mathrm{GL}_2(K_0)$ be the element whose underlying matrix is $\mathrm{diag}(\pi, 1)$. Let $N$ be a subgroup of $\mathrm{PGL}(2, K_0)$ acting on the Bruhat–Tits tree `BruhatTits.tree 𝒪 K₀`, whose vertices are homothety classes of full $\mathcal{O}$-lattices in $K_0^2$ and whose edges come from adjacency of lattices. Assume $N$ is Schottky for this action in the sense that every vertex has trivial stabiliser in $N$, no element of $N$ carries a dart to its reverse, and $N$ has finitely many orbits both on vertices and on darts; assume moreover that every element of $N$ preserves the parity of the graph distance to the vertex `stdVertex 𝒪 K₀` attached to the standard lattice. The conclusion is that the type `MumfordGlueCore 𝒪 π K₀ r g₁ N` is nonempty: there exists a tower of schemes $Z_n$ over $\mathrm{Spec}(\mathcal{O}/\pi^{n+1})$, flat and separated over their bases, with transition maps $zt_n : Z_n \to Z_{n+1}$ exhibiting each $Z_n$ as the pullback of $Z_{n+1}$ along $\mathrm{Spec}(\mathcal{O}/\pi^{n+1}) \to \mathrm{Spec}(\mathcal{O}/\pi^{n+2})$, together with edge charts $\zeta_{h,n}$ indexed by $h \in \mathrm{GL}_2(K_0)$, which are open immersions over the base, compatible with the transition maps, cover each $Z_n$ by finitely many of them, and are invariant under left multiplication of $h$ by elements of $N$, together with the vertex-chart algebra maps $\iota_n$ and their relations `ι_ξ`, `ι_η` and `ι_isLocalization`, the chart transports $\tau$ and $\alpha$ with their defining properties, the edge and vertex incidence conditions `ζ_edge`, `ζ_vertex`, the overlap bound `ζ_preimage_le`, and the descent field `desc`.
--
--   This is the existence statement for the gluing data underlying Mumford's analytic construction of degenerating curves, in the form used for the Čerednik–Drinfeld uniformisation: the whole $\pi$-adic tower of reductions of the quotient of the formal upper half plane by a type-preserving Schottky group $N$, presented by edge and vertex charts. It is used by [`CerednikDrinfeld.FormalOmega.nonempty_mumfordGlue_of_isSchottky`](thm.html#CerednikDrinfeld.FormalOmega.nonempty_mumfordGlue_of_isSchottky), which passes from this level-by-level core to the glued formal object.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_nonempty_mumfordGlueCore_of_isSchottky.lean

import Definitions.Def_CerednikDrinfeld_MumfordGlueCore
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordVertexType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.FormalOmega.nonempty_mumfordGlueCore_of_isSchottky
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (hN : IsSchottky (↥N) (BruhatTits.tree 𝒪 K₀))
    (hNtype : N ≤ typePreserving (PGL(2, K₀)) (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀)) :
    Nonempty (MumfordGlueCore 𝒪 π K₀ r g₁ N) := by sorry
