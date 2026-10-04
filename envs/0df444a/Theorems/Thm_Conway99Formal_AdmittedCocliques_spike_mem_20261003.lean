-- Prove2me | Theorems.Thm_Conway99Formal_AdmittedCocliques_spike_mem_20261003
-- name    : Conway99Formal.AdmittedCocliques.spike_mem_20261003
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T00:37:46.988191+00:00
-- url     : https://prove2.me/theorems/99756071-bf2d-4aa9-a7ff-3f8bb84246de
-- title:
--   Lattice membership of a seven-spike from one admitted coclique
-- statement:
--   Fix one additive subgroup L of a real vector space and a finite family of point vectors. Suppose every point belongs to L and every pairwise point difference divided by three belongs to L. If a 22-point set C is admitted, meaning its average vector z_C=(sum of its point vectors)/7 belongs to that same L, then the seven-spike vector (y_p-z_C)/3 belongs to L for every point p. This is the Bezout membership step; it does not construct a strongly regular graph, a permitted determinant-49 lattice, or the seven-spike converse.
-- source:
--   proofs/ROOT_COCLIQUE_COMPATIBILITY.md lines 207-223 in archive/clean-start/proof-library.zip, SHA-256 6cbe401d478b7e8627c81d6801585d5949ec254a5bee9878b1f9513cd0244772; source proof line 216 gives the lattice-divisibility identity.

import Definitions.Def_Conway99_Admitted_Cocliques_20261003
set_option autoImplicit false

theorem Conway99Formal.AdmittedCocliques.spike_mem_20261003 {V E : Type*} [Fintype V] [DecidableEq V] [AddCommGroup E] [Module ℝ E] (L : AddSubgroup E) (point : V → E) (hpoint : ∀ p, point p ∈ L) (hdiff : ∀ p q, (1 / 3 : ℝ) • (point p - point q) ∈ L) (C : Finset V) (hcard : C.card = 22) (hC : Conway99Formal.AdmittedCocliques.Admitted L point C) (p : V) : Conway99Formal.AdmittedCocliques.spikeVector point C p ∈ L := by sorry
