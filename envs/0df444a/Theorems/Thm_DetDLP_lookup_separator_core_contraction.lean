-- Prove2me | Theorems.Thm_DetDLP_lookup_separator_core_contraction
-- name    : DetDLP.lookup_separator_core_contraction
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T15:46:41.089121+00:00
-- url     : https://prove2.me/theorems/0018210f-9299-42ec-8d41-8c448041a528
-- title:
--   Exact lookup cut with one boundary bit per subdivision vertex
-- statement:
--   Removing the designated lookup vertices produces an explicit bipartite core with at most S edges and maximum degree at most D. The actual cut edges are in bijection with the 4mk distinct subdivision vertices. In every commutative ring the full contraction is the sum over boundary bit assignments of the original lookup entries times the corresponding core contraction. Each core tensor depends only on the boundary bit at its own subdivision vertex, if it has one. All original lookup port indices are retained.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Section 4.2 and the lookup/core identity used in Section 5.3.

import Definitions.Def_DetDLP_TerminalBTN

set_option autoImplicit false
open Finset

namespace DetDLP

theorem lookup_separator_core_contraction {G : BipartiteMultigraph} {m k S D : ℕ}
    (s : LookupSeparatorSpec G m k S D) :
    let B := {e : Fin G.nE // (G.endpoints e).1∈s.lookupVerts ∨ (G.endpoints e).2∈s.lookupVerts}
    ∃ H : BipartiteMultigraph, ∃ old : Fin H.nV ≃ {v : Fin G.nV // v∉s.lookupVerts},
    ∃ host : B ≃ ↥s.termSubdivVerts, ∃ port : (v : ↥s.lookupVerts)→Fin (G.deg v.val)→B,
      H.nE≤S ∧ H.nV≤G.nV ∧ H.maxDeg≤D ∧ Fintype.card B=4*m*k ∧
      (∀ v i,(port v i).val=(G.ports v.val).get i) ∧
      ∀ (R : Type) [CommRing R] (T : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→R),
      ∃ A : (B→Bool)→(v : Fin H.nV)→(Fin (H.deg v)→Bool)→R,
        (∀ η θ v,(∀ e,(host e).val=(old v).val→η e=θ e)→A η v=A θ v) ∧
        BTNContract G T=∑ η : B→Bool,(∏ v : {v : Fin G.nV // v∈s.lookupVerts},
          T v.val (fun i => η (port v i)))*BTNContract H (A η) := by sorry

end DetDLP
