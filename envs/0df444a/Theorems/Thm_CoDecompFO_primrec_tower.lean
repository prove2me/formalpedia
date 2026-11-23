-- Prove2me | Theorems.Thm_CoDecompFO_primrec_tower
-- name    : CoDecompFO.primrec_tower
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:57:50.962357+00:00
-- url     : https://prove2.me/theorems/82d5b703-4786-4f8a-92d9-ad828e2c01d8
-- title:
--   The explicit tower of hypothetical counts is primitive recursive
-- statement:
--   The explicit bound
--   $$
--   T_0(w,q)=2^{2^q},\qquad
--   T_{m+1}(w,q)=2^{w\,2^{wT_m(w,q)}}
--   $$
--   used in Lemma 5.81 is primitive recursive as a function of $(w,q,m)$. This supplies the computable numerical size bound required by the bottom-up hypothetical-table implementation.
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), Lemma 5.81 and ¶5.82, p.41. Primitive recursiveness is the computational ingredient implicit in the proof of Theorem 1.16 that the tables and their explicit size bound can be computed from the decomposition.

import Definitions.Def_CoDecompFO_HTh
import Mathlib.Computability.Partrec

set_option autoImplicit false

/-- The explicit tower bound is primitive recursive in the width, atom count, and level. -/
theorem CoDecompFO.primrec_tower :
    Primrec (fun a : (ℕ × ℕ) × ℕ => tower a.1.1 a.1.2 a.2) := by sorry
