-- Prove2me | Theorems.Thm_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver
-- name    : AlgebraicGeometry.prodKerGraph_comap_mapOnProdOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/94812653-0581-57b6-8204-dd62a6b002c0
-- title:
--   Naturality of the graph-product ideal sheaf under base change
-- statement:
--   Let $f \colon \mathcal{C} \to S$ be a separated morphism of schemes, let $r$ be a natural number, and let $T, T'$ be schemes equipped with morphisms $g \colon T \to S$ and $g' \colon T' \to S$. Let $a \colon \mathrm{Fin}\,r \to (T' \to \mathcal{C})$ be a family of morphisms with $a_i$ followed by $f$ equal to $g'$ for every $i$, i.e. a family of $r$ points of $\mathcal{C}$ over $S$ parametrised by $T'$, and let $\varphi \colon T \to T'$ satisfy $\varphi$ followed by $g'$ equal to $g$. For a point $b \colon T' \to \mathcal{C}$ over $S$, write $\Gamma_b =$ `graphOver` for the induced section $T' \to \mathcal{C} \times_S T'$ with components $b$ and $\mathrm{id}_{T'}$, and let `prodKerGraph` be the product, over $i \in \mathrm{Fin}\,r$, of the kernel ideal sheaves of the sections $\Gamma_{a_i}$, an ideal sheaf datum on $\mathcal{C} \times_S T'$. Write `mapOnProdOver` for the morphism $\mathcal{C} \times_S T \to \mathcal{C} \times_S T'$ obtained from $\mathrm{id}_{\mathcal{C}}$, $\varphi$ and $\mathrm{id}_S$. The assertion is that the inverse image along this morphism of $\prod_i \ker \Gamma_{a_i}$ equals $\prod_i \ker \Gamma_{\varphi \text{ followed by } a_i}$, the corresponding product formed from the composed family $i \mapsto \varphi$ followed by $a_i$, whose compatibility with $g$ follows from associativity together with the two hypotheses.
--
--   This is the naturality in the parameter scheme of the assignment sending an $r$-tuple of $S$-points of $\mathcal{C}$ to the product of the ideal sheaves of their graphs: pulling that ideal sheaf back along $\varphi$ produces the ideal sheaf attached to the composed tuple, so the construction behaves like a family of relative divisors over the base of parameters. It is used in the study of the tautological family of degree-$r$ divisors on $\mathcal{C}$ over $S$, in particular by the results producing sum maps of relative effective Cartier divisors and the identification of such divisors as products of graph kernels over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver.lean

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.prodKerGraph_comap_mapOnProdOver
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] {r : ℕ} {T T' : Scheme.{u}} {g : T ⟶ S}
    {g' : T' ⟶ S} (a : Fin r → (T' ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g') (φ : T ⟶ T')
    (hφ : φ ≫ g' = g) :
    (prodKerGraph f a ha).comap (mapOnProdOver f φ hφ) =
      prodKerGraph f (fun i => φ ≫ a i) (fun i => by rw [Category.assoc, ha, hφ]) := by sorry
