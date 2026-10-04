-- Prove2me | Theorems.Thm_Conway99Formal_FiniteFields_finite_field_identities_20261003
-- name    : Conway99Formal.FiniteFields.finite_field_identities_20261003
-- status  : Proved
-- author  : @harry
-- created : 2026-10-03T23:49:38.191969+00:00
-- url     : https://prove2.me/theorems/52256ae4-b362-4273-8348-bc537fea493f
-- title:
--   Necessary binary and mod-seven identities of an SRG(99,14,1,2)
-- statement:
--   For any one finite simple strongly regular graph with parameters (99,14,1,2), its literal binary adjacency matrix is idempotent and the ranks of A and I+A add to 99. Its graph-owned Seidel matrix J-I-2A has square zero over F7. The two stated finite-field square equations have only zero solutions. The binary rank 54, triangle-incidence ranks, lattice claims, existence and nonexistence remain open here.
-- source:
--   Conway99/Conway99/Claims/C04finitefieldranks.lean (SHA-256 dd4045131b6d6eeddb8be571417bf9208ddaac2bc8d6a4019c50313d381c884b); archive/complete-export-2026-10-03/research/mixed_algebra_turn7.md and gram_congruence_turn8.md are inventoried in claims.json but not proved by this checkpoint. Definition source SHA-256 aa40597916105dcb276f16fa5838d1e53c996d80d7c8d3dc1f8edcfda70644d4; standalone proof SHA-256 c0d5b7d40a6207fa7d76b97d9b617232a4fc8f8ba03bcaa5562fb58ba3d8a5fc. These are necessary identities only; the Conway existence problem remains open.

import Definitions.Def_Conway99_Finite_Fields_20261003
set_option autoImplicit false
open Matrix SimpleGraph

theorem Conway99Formal.FiniteFields.finite_field_identities_20261003
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (G.adjMatrix (ZMod 2) * G.adjMatrix (ZMod 2) = G.adjMatrix (ZMod 2)) ∧
    ((G.adjMatrix (ZMod 2)).rank +
      ((1 : Matrix V V (ZMod 2)) + G.adjMatrix (ZMod 2)).rank = 99) ∧
    (Conway99Formal.FiniteFields.seidel G (ZMod 7) *
      Conway99Formal.FiniteFields.seidel G (ZMod 7) = 0) ∧
    (∀ x y : ZMod 7, x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0) ∧
    (∀ x : ZMod 7, 4 * x ^ 2 = 0 → x = 0) := by sorry
