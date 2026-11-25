-- Prove2me | Theorems.Thm_DetDLP_stopped_terminal_residual_network
-- name    : DetDLP.stopped_terminal_residual_network
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T16:22:40.415949+00:00
-- url     : https://prove2.me/theorems/b436d35b-ab4e-47d4-9adf-ffcf4a7406f7
-- title:
--   Reattaching stopped core tensors to the original lookup ports
-- statement:
--   For any assignment of the actual boundary edges to n stopped core tensors, there is a bipartite residual network with exactly 4mk edges and 4m+n vertices. Each lookup vertex retains degree k and the original port order. Each stopped vertex has degree exactly the size of its assigned boundary fiber. In every commutative ring the residual contraction equals the sum over all boundary assignments of the product of the original lookup entries and the stopped tensor entries. A common upper bound on the fiber cardinalities gives the stated maximum degree.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Section 5.3, construction and tensor identity for each residual network in the terminal expansion.

import Definitions.Def_DetDLP_TerminalBTN

set_option autoImplicit false
open Finset

namespace DetDLP

theorem stopped_terminal_residual_network {G : BipartiteMultigraph} {m k S D n : ℕ} (s : LookupSeparatorSpec G m k S D) :
    let B := {e : Fin G.nE // (G.endpoints e).1∈s.lookupVerts ∨ (G.endpoints e).2∈s.lookupVerts}
    ∀ (leaf : B→Fin n) (U : ℕ), (∀ j,Fintype.card {e : B // leaf e=j}≤U) →
    ∃ (H : BipartiteMultigraph) (vertices : (↥s.lookupVerts ⊕ Fin n) ≃ Fin H.nV)
      (boundaryPort : (v : ↥s.lookupVerts)→Fin (G.deg v.val)→B),
      H.nE=4*m*k ∧ H.nV=4*m+n ∧ H.maxDeg ≤ max k U ∧
      (∀ v,H.deg (vertices (.inl v))=k) ∧
      (∀ j,H.deg (vertices (.inr j))=Fintype.card {e : B // leaf e=j}) ∧
      (∀ v i,(boundaryPort v i).val=(G.ports v.val).get i) ∧
      ∀ (R : Type) [CommRing R] (T : (v : ↥s.lookupVerts)→(Fin (G.deg v.val)→Bool)→R)
        (F : (j : Fin n)→({e : B // leaf e=j}→Bool)→R),
      ∃ A : (v : Fin H.nV)→(Fin (H.deg v)→Bool)→R, BTNContract H A =
        ∑ x : B→Bool,(∏ v,T v (fun i => x (boundaryPort v i)))*
          ∏ j,F j (fun e => x e.val) := by sorry
end DetDLP
