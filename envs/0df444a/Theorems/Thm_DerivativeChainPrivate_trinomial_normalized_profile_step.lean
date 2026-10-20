-- Prove2me | Theorems.Thm_DerivativeChainPrivate_trinomial_normalized_profile_step
-- name    : DerivativeChainPrivate.trinomial_normalized_profile_step
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-19T05:07:17.783706+00:00
-- url     : https://prove2.me/theorems/7d5edad4-b287-4664-9a1a-5d50c95aa3e2
-- title:
--   The normalized trinomial profile satisfies a Bernoulli step bound
-- statement:
--   For real x,d,e with 0<d<=e<x, the ratio (1-d/x) to the real power e/d, divided by 1-e/x, is at least one. This is the positive normalized-profile comparison used in the trinomial branch analysis; it does not assert the full trinomial chain theorem.
-- source:
--   Derivative-zero chains: public formalization reference, R49, DerivativeChainPrivate.trinomial_normalized_profile_step. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false

theorem DerivativeChainPrivate.trinomial_normalized_profile_step (x d e : ℝ)
    (hd : 0 < d) (hde : d ≤ e) (hex : e < x) :
    1 ≤ (1 - d / x) ^ (e / d) / (1 - e / x) := by sorry
