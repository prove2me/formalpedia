-- Prove2me | Theorems.Thm_CerednikDrinfeld_BruhatTits_exists_iso_tree_baseChange
-- name    : CerednikDrinfeld.BruhatTits.exists_iso_tree_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/2f563d40-9fe2-53d9-8612-af63c8232236
-- title:
--   Functoriality of the Bruhat–Tits tree in the pair (R,K)
-- statement:
--   Let $R'$ and $R$ be discrete valuation domains with fraction fields $K'$ and $K$ respectively (the fraction-field structure being given by algebra maps $R'\to K'$, $R\to K$ exhibiting $K'$, $K$ as localisations). Let $\iota$ be an integral homomorphism from $(R',K')$ to $(R,K)$, that is, a ring homomorphism $\iota_{K}\colon K'\to K$ together with a ring homomorphism $R'\to R$ commuting with the two structure maps, and let $\iota'$ be an integral homomorphism in the opposite direction; assume the two field maps are mutually inverse, $\iota_{K}(\iota'_{K}(x))=x$ for all $x\in K$ and $\iota'_{K}(\iota_{K}(x))=x$ for all $x\in K'$. Then there exists an isomorphism $e$ of simple graphs from the Bruhat–Tits tree of $(R',K')$ to that of $(R,K)$ — vertices being homothety classes of full lattices in $K'^2$, resp. $K^2$, and edges being the symmetrisation of the relation that the classes have representatives $L$, $L'$ with $L$, $L'$ adjacent — such that: $e$ sends every vertex $v$ to its base change along $\iota$, the class of the $R$-span of the image of a representative lattice under the coordinatewise map induced by $\iota_{K}$; the inverse $e^{-1}$ is likewise base change along $\iota'$; $e$ is equivariant for the actions of $\mathrm{GL}_2(K')$ and $\mathrm{GL}_2(K)$ along the induced group homomorphism $\mathrm{GL}_2(K')\to\mathrm{GL}_2(K)$ obtained by applying $\iota_{K}$ entrywise, i.e. $e(g\cdot v)=\iota(g)\cdot e(v)$; and $e$ carries the standard vertex, the class of the lattice of vectors both of whose coordinates are integral over the base, to the standard vertex.
--
--   This is the statement that the tree of $\mathrm{PGL}_2$ attached to a discrete valuation ring and its fraction field depends on the pair only up to isomorphism, in the form needed to transport vertex- and action-theoretic statements between isomorphic copies of a valued field (for instance between a $v$-adic completion and its image inside a larger complete field). It is used by [`CerednikDrinfeld.BruhatTits.exists_iso_tree_mulEquiv_projGenLinGroup_baseChange`](thm.html#CerednikDrinfeld.BruhatTits.exists_iso_tree_mulEquiv_projGenLinGroup_baseChange), which upgrades the equivariance here to the level of projective linear groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_BruhatTits_exists_iso_tree_baseChange.lean

import Definitions.Def_LatticeTreeBaseChange
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CerednikDrinfeld.BruhatTits.exists_iso_tree_baseChange
    (R' K' R K : Type) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Field K'] [Algebra R' K']
    [IsFractionRing R' K'] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K]
    (ι : LT.LatticeTree.IntegralHom R' K' R K) (ι' : LT.LatticeTree.IntegralHom R K R' K')
    (h₁ : ∀ x : K, ι.toField (ι'.toField x) = x) (h₂ : ∀ x : K', ι'.toField (ι.toField x) = x) :
    ∃ e : CerednikDrinfeld.BruhatTits.tree R' K' ≃g CerednikDrinfeld.BruhatTits.tree R K,
      (∀ v : LT.LatticeTree.Vertex R' K', e v = LT.LatticeTree.Vertex.baseChange ι v) ∧
      (∀ v : LT.LatticeTree.Vertex R K, e.symm v = LT.LatticeTree.Vertex.baseChange ι' v) ∧
      (∀ (g : GL (Fin 2) K') (v : LT.LatticeTree.Vertex R' K'), e (g • v) = ι.mapGL g • e v) ∧
      e (LT.LatticeTree.stdVertex R' K') = LT.LatticeTree.stdVertex R K := by sorry
