-- Prove2me | Theorems.Thm_Conway99Formal_OrdinaryEdgeLabels_repeated_distinct_negative_edges_short_kernel
-- name    : Conway99Formal.OrdinaryEdgeLabels.repeated_distinct_negative_edges_short_kernel
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T02:24:43.105574+00:00
-- url     : https://prove2.me/theorems/c7941946-3946-49c1-a53c-456b1e7a02e1
-- title:
--   Short lattice kernel vector from equal labels on distinct negative graph edges
-- statement:
--   For one hypothetical SRG(99,14,1,2) equipped with the explicit OrdinaryData frame, minimum and common-lattice bridges, two distinct actual negative graph edges with equal operator-produced vector labels yield a nonzero vector in the same starting lattice and the operator kernel. Its squared norm is 6, 8, 10 or 12. The conclusion does not force labels to repeat and does not contradict rootlessness.
-- source:
--   archive/clean-start/proof-library.zip member proofs/MINIMUM_EDGE_LABEL_COMPATIBILITY.md lines 264-295; source hash and unresolved graph-to-lattice bridges in claims.json. Checked local proof: server-package/Solutions/Sol_ShortKernel.lean.

import Definitions.Def_Conway99_OrdinaryEdgeLabels_20261003
set_option autoImplicit false
open Conway99Formal.OrdinaryEdgeLabels

theorem Conway99Formal.OrdinaryEdgeLabels.repeated_distinct_negative_edges_short_kernel
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (d : OrdinaryData G)
    (a b c e : V) (hab : G.Adj a b) (hce : G.Adj c e)
    (hnegab : d.discrepancy a b = -1)
    (hnegce : d.discrepancy c e = -1)
    (hdistinct : ¬(a = c ∧ b = e) ∧ ¬(a = e ∧ b = c))
    (hlabels : labelVector d a b = labelVector d c e) :
    repeatedKernelVector d a b c e ∈ d.startingLattice ∧
      d.op d.ordinary (repeatedKernelVector d a b c e) = 0 ∧
      repeatedKernelVector d a b c e ≠ 0 ∧
      (‖repeatedKernelVector d a b c e‖ ^ 2 = 6 ∨
        ‖repeatedKernelVector d a b c e‖ ^ 2 = 8 ∨
        ‖repeatedKernelVector d a b c e‖ ^ 2 = 10 ∨
        ‖repeatedKernelVector d a b c e‖ ^ 2 = 12) := by sorry
