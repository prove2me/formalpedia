-- Prove2me | Theorems.Thm_DetDLP_d4_core_cut_poly_and_spec
-- name    : DetDLP.d4_core_cut_poly_and_spec
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T09:08:35.537367+00:00
-- url     : https://prove2.me/theorems/be9a328a-3ea8-46b3-812c-230a65a505e4
-- title:
--   Canonical polynomial-time core deletion and pinned contraction
-- statement:
--   The polynomial-time bit-string algorithm emits the exact encoded graph and boundary tables of the canonical induced core. Its edges, vertices, and maximum degree obey the separator bounds. There are exactly four times the product of block count and lookup arity boundary edges, with at most one at each host. Over every commutative ring the original contraction is the sum over these boundary bits of the lookup product times the core contraction, with each original tensor port explicitly read from either its boundary index or its internal core-port index.

import Definitions.Def_DetDLP_D4CoreCut
open DetDLP DetDLP.D4CoreCut Finset
set_option autoImplicit false

theorem DetDLP.d4_core_cut_poly_and_spec : Groundwork.PolyT cutCoreRaw ∧ ∀ {C c : ℕ} (x : D4Plan.Input C c),
    let L := x.spec.lookupVerts
    let t := cutCore x.G L (independent_of_spec x.G x.spec)
    cutCoreRaw (D4Plan.input x) = t.encode x.G L ∧ t.H₀.nE ≤ x.S ∧ t.H₀.nV ≤ x.G.nV ∧
    t.H₀.maxDeg ≤ C * Nat.ceil ((x.b : ℝ)^((3:ℝ)/4)) ∧ t.boundary.length = 4*x.m*x.k ∧
    (∀ z,(univ.filter fun y => t.host z = t.host y).card ≤ 1) ∧
    ∀ (A : Type) [CommRing A] (T : (v : Fin x.G.nV) → (Fin (x.G.deg v) → Bool) → A),
    let bit := fun (η : Fin (4*x.m*x.k) → Bool) (e : Fin x.G.nE) => (List.ofFn η).getD (t.boundary.idxOf e) false
    let pin := fun (η : Fin (4*x.m*x.k) → Bool) (v : Fin t.H₀.nV) (a : Fin (t.H₀.deg v) → Bool) =>
      T (t.orig v) (fun j =>
        let e := (x.G.ports (t.orig v)).get j
        if e ∈ t.boundary then bit η e else
          let i := (coreEdges x.G L).idxOf e
          (List.ofFn a).getD ((t.H₀.ports v).map Fin.val |>.idxOf i) false)
    BTNContract x.G T = ∑ η : Fin (4*x.m*x.k) → Bool,
      (∏ v : ↥L,T v.val (fun j => bit η ((x.G.ports v.val).get j))) * BTNContract t.H₀ (pin η) := by sorry
