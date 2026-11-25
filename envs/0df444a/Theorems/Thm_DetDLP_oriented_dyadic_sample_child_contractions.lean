-- Prove2me | Theorems.Thm_DetDLP_oriented_dyadic_sample_child_contractions
-- name    : DetDLP.oriented_dyadic_sample_child_contractions
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T15:20:25.69085+00:00
-- url     : https://prove2.me/theorems/ff2fa723-9ecc-4726-9524-ea650c8f9c3b
-- title:
--   Weighted child contractions of the original oriented dyadic sample
-- statement:
--   Every real edge of the original bipartite multigraph occupies one packet slot. At a nonzero dyadic node, the split-assignment sum using the actual finite-precision packet selectors equals a sum of products of child tensor-network contractions, restricted to modes whose total weight is less than the precision. Each original endpoint contributes one edge in its assigned group. Each child has precisely the original vertices assigned to its group plus one vertex per packet. Its maximum degree obeys the two local port-count bounds. The same graphs and mode assignments work for every tuple of terminal data, and each child tensor takes only its own terminal argument.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Sections 5.1 and 5.3, finite-precision recurrence at a nonzero grid node with actual input graph and terminal assignments.

import Definitions.Def_DetDLP_OrientedPacketInstance

set_option autoImplicit false
open Polynomial Finset

namespace DetDLP

theorem oriented_dyadic_sample_child_contractions {a p : ℕ} (i : Fin a) (hp : 0<p)
    (t : ZMod (2^(a+1))) (ht : t≠0) (hi : padicValNat 2 t.val=i.val) :
    ∃ U : ZMod (2^(a+1)) → (ZMod (2^p))[X], OrientedPacketInstance.Represents t U ∧
    ∀ {r : ℕ} (P R : Type) [Fintype P] [DecidableEq P] [CommRing R] [Algebra (ZMod (2^p)) R]
      (G : BipartiteMultigraph) (active : P→Finset (Fin (2^a))) (layout : Fin G.nE ≃ OrientedPacketInstance.Address active)
      (tag : P→Fin r×Fin r) (grp : Fin G.nV→Fin r),
      (∀ e d,OrientedPacketInstance.group i (tag (layout e).1) d (layout e).2.val.val=grp (OrientedPacketInstance.endpoint G e d)) →
      ∀ (T : Fin r→Type) (V : (v : Fin G.nV)→T (grp v)→(Fin (G.deg v)→Bool)→R) (z : R),
      let E := OrientedPacketInstance.Assigned i tag active
      let J := OrientedPacketInstance.Mode i tag p
      let beta := ∀ h,J h→Fin p
      let weight (b : beta) := ∑ h,∑ j : J h,(j.2.val+1)*(b h j).val
      ∃ H : Fin r→BipartiteMultigraph,
        (∀ g,(H g).nE=Fintype.card (E g) ∧ (H g).nV=Fintype.card {v : Fin G.nV // grp v=g}+Fintype.card P) ∧
        (∀ g D, (∀ v : Fin G.nV,Fintype.card {e : E g // OrientedPacketInstance.endpoint G
          (layout.symm ⟨e.val.1,e.val.2.1,e.property.1⟩) e.val.2.2=v} ≤ D) →
          (∀ q : P,Fintype.card {e : E g // e.val.1=q} ≤ D) → (H g).maxDeg≤D) ∧
        ∃ child : beta → (g : Fin r) → T g → (v : Fin (H g).nV) → (Fin ((H g).deg v)→Bool) → R,
          ∀ τ : ∀ g,T g,
            (∑ x : Fin G.nE→Bool,∑ y : Fin G.nE→Bool,
              DeformedContraction.weight (fun v => V v (τ (grp v))) x y *
                ∏ e,OrientedPacketInstance.selector G active layout U z x y e) =
            ∑ b ∈ univ.filter (fun b => weight b<p),(2:R)^(weight b)* ∏ g,BTNContract (H g) (child b g (τ g)) := by sorry

end DetDLP
