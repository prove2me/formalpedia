-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_edge_nondeg_saturation_of_valuationRing
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.exists_edge_nondeg_saturation_of_valuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/ba20c121-68c3-5b31-9b2e-c00c7a92058e
-- title:
--   Deligne's edge condition for saturated lines over a valuation ring
-- statement:
--   Let $\mathcal O$ be a discrete valuation domain with fraction field $K$ and let $\pi \in \mathcal O$ be irreducible. Let $V$ be a valuation domain that is an $\mathcal O$-algebra with $\pi \mapsto 0$ in $V$, and let $L$ be a field that is both an $\mathcal O$-algebra and a $V$-algebra, compatibly, and is the fraction field of $V$. Let $d$ be a Deligne datum over $L$ for $\pi$, that is, an assignment $M \mapsto d.\mathrm{line}\,M$ of an $L$-submodule of $L \otimes_{\mathcal O} M$ to every full lattice $M \subseteq K^2$ (a finitely generated $\mathcal O$-submodule of $\mathrm{Fin}\,2 \to K$ spanning $K^2$ over $K$) with invertible quotients, monotone under inclusions of lattices, equivariant for scalar homotheties, and satisfying the edge condition at every prime of $L$. Let $\mathfrak p$ be a prime ideal of $V$. Then there exist full lattices $M' \subseteq M$ in $K^2$ such that: $\pi v \in M'$ for every $v \in M$; for every $v \in M$ with $v \notin M'$, the element $1 \otimes v$ of $V \otimes_{\mathcal O} M$ lies outside the sum of $\mathfrak p \cdot (V \otimes_{\mathcal O} M)$ with the $V$-span of the saturation $\{x \in V \otimes_{\mathcal O} M : x \text{ maps into } d.\mathrm{line}\,M \text{ in } L \otimes_{\mathcal O} M\}$; and for every $v' \in M'$ that is not of the form $\pi w$ with $w \in M$, the element $1 \otimes v'$ lies outside the corresponding sum $\mathfrak p \cdot (V \otimes_{\mathcal O} M')$ plus the $V$-span of the saturation of $d.\mathrm{line}\,M'$.
--
--   This is Deligne's non-degeneracy (edge) condition $(*)$, in the exact form of the `nondeg` field of `DeligneDatum`, verified at an arbitrary prime $\mathfrak p$ of $V$ for the family obtained from a Deligne datum over $L$ by saturating its lines inside $V \otimes_{\mathcal O} M$. It supplies the edge-condition part of [`CerednikDrinfeld.FormalOmega.DeligneDatum.exists_isBaseChange_of_valuationRing_of_map_eq_zero`](thm.html#CerednikDrinfeld.FormalOmega.DeligneDatum.exists_isBaseChange_of_valuationRing_of_map_eq_zero), which descends a Deligne datum over the fraction field $L$ to one over the valuation ring $V$; the remaining fields of the descended datum come from the generic saturation lemma for invertible quotients over a valuation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_edge_nondeg_saturation_of_valuationRing.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_edge_nondeg_saturation_of_valuationRing
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π)
    (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra 𝒪 V] (hV : algebraMap 𝒪 V π = 0)
    (L : Type) [Field L] [Algebra 𝒪 L] [Algebra V L] [IsScalarTower 𝒪 V L] [IsFractionRing V L]
    (d : DeligneDatum (K := K) π L) (𝔭 : Ideal V) (h𝔭 : 𝔭.IsPrime) :
    ∃ (M' M : FullLattice 𝒪 K) (_ : M'.1 ≤ M.1),
      (∀ v : ↥M.1, (algebraMap 𝒪 K π) • (v : Fin 2 → K) ∈ M'.1) ∧
      (∀ v : ↥M.1, (v : Fin 2 → K) ∉ M'.1 →
        (1 : V) ⊗ₜ[𝒪] v ∉ Submodule.span V {x : latticeBaseChange 𝒪 K V M |
            LinearMap.rTensor (↥M.1) (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap x ∈ d.line M}
          ⊔ (𝔭 • ⊤ : Submodule V (latticeBaseChange 𝒪 K V M))) ∧
      (∀ v' : ↥M'.1, (¬ ∃ w : ↥M.1, (v' : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K)) →
        (1 : V) ⊗ₜ[𝒪] v' ∉ Submodule.span V {x : latticeBaseChange 𝒪 K V M' |
            LinearMap.rTensor (↥M'.1) (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap x ∈ d.line M'}
          ⊔ (𝔭 • ⊤ : Submodule V (latticeBaseChange 𝒪 K V M'))) := by sorry
