-- Prove2me | Theorems.Thm_DetDLP_d4_reattach_poly_and_spec
-- name    : DetDLP.d4_reattach_poly_and_spec
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T08:57:23.603808+00:00
-- url     : https://prove2.me/theorems/d7ff6614-f9c8-4d55-914e-da6d3bdd4b33
-- title:
--   Canonical polynomial-time lookup reattachment and contraction
-- statement:
--   From the terminal instance, a unary count of stopped leaves, and the binary list of leaf indices, a polynomial-time function emits exactly the explicit residual graph. The graph has four times the block count plus the leaf count vertices and one edge per boundary bit. The degree is bounded by the larger of the lookup arity and the maximum leaf fiber. Over every commutative ring its contraction splits into a product of original lookup entries and stopped-leaf entries summed over the boundary bits in their original edge order.

import Definitions.Def_DetDLP_D4CoreCut
open DetDLP DetDLP.D4CoreCut Finset
set_option autoImplicit false

theorem DetDLP.d4_reattach_poly_and_spec : Groundwork.PolyT reattachRaw ∧ ∀ {C c : ℕ} (x : D4Plan.Input C c) (n : ℕ),
    let L := x.spec.lookupVerts
    let B := D4CoreCut.B x.G L
    ∀ (f : B → Fin n), let H := reattach x.G L n f
    reattachRaw (reattachInput (D4Plan.input x) n (List.ofFn fun i => (f i).val)) = H.encode ∧
    H.nE = 4*x.m*x.k ∧ H.nV = 4*x.m+n ∧
    (∀ U : ℕ, (∀ j,Fintype.card {i : B // f i=j} ≤ U) → H.maxDeg ≤ max x.k U) ∧
    ∃ (old : Fin L.card ≃ ↥L) (rank : B ≃ Fin (4*x.m*x.k))
      (lp : (v : Fin L.card) → Fin (x.G.deg (old v).val) ≃ Fin (H.deg (v.castAdd n)))
      (rp : (j : Fin n) → Fin (H.deg (Fin.natAdd L.card j)) ≃ {e : B // f e=j}),
    (∀ i,(rank i).val=i.val) ∧
    (∀ v i, origB x.G L ((H.ports (v.castAdd n)).get (lp v i)) = (x.G.ports (old v).val).get i) ∧
    (∀ j i,(rp j i).val = (H.ports (Fin.natAdd L.card j)).get i) ∧
    ∀ (A : Type) [CommRing A] (T : (v : ↥L) → (Fin (x.G.deg v.val) → Bool) → A)
      (F : (j : Fin n) → ({e : B // f e=j} → Bool) → A),
    let combined : (v : Fin H.nV) → (Fin (H.deg v) → Bool) → A := Fin.addCases
      (fun v t => T (old v) (fun i => t (lp v i))) (fun j t => F j (fun e => t ((rp j).symm e)))
    BTNContract H combined = ∑ η : Fin (4*x.m*x.k) → Bool,
      (∏ v : Fin L.card, T (old v) (fun i => η (rank ((H.ports (v.castAdd n)).get (lp v i)))))*
      ∏ j : Fin n, F j (fun e => η (rank e.val)) := by sorry
