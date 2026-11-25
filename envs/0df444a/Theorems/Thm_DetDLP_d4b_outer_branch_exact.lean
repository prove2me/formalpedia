-- Prove2me | Theorems.Thm_DetDLP_d4b_outer_branch_exact
-- name    : DetDLP.d4b_outer_branch_exact
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T08:11:27.778248+00:00
-- url     : https://prove2.me/theorems/4b4a60f6-513a-4c22-b840-78818e23846a
-- title:
--   Exact reconstruction of a supplied residual branch
-- statement:
--   For an arbitrary specified monic modulus and residual tensor network, canonical answers to every scalar digit query determine bounded coefficient vectors. Combining those vectors by the residual unpacking map recovers the contraction of this same tensor network.
-- source:
--   Branch reconstruction in the accepted terminal contraction proof, submission 4976ab83-8b47-4ab9-9e29-85817d1dcc05.

import Definitions.Def_DetDLP_ResidualScalarOracle
set_option autoImplicit false
open Polynomial DetDLP DetDLP.ResidualScalarOracle

theorem DetDLP.d4b_outer_branch_exact (f : ℤ[X]) (ell q : ℕ) (hf : f.Monic) (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → B f ell q) (hq : 0 < q)
    (h J β : ℕ) (cover : q ≤ h * J) (edges : G.nE ≤ β) (w : (Fin G.nV → Fin J) → List Bool)
    (eval : ∀ a, EncodesTruncPoly (precision f ell G h β) (spacing f G * ell) (w a)
      (BTNContract G (query f ell q hf G T J h β a))) :
    ∃ c : (Fin G.nV → Fin J) → Fin (spacing f G * ell) → ℕ,
      (∀ a, w a = encodeNatListBin (List.ofFn (c a))) ∧
      (∀ a i, c a i < 2 ^ precision f ell G h β) ∧ unpack f ell q G h J c = BTNContract G T := by sorry
