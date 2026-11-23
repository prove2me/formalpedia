-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_proposition_16_exact_size
-- name    : ChvatalOneHard398.SAT.proposition_16_exact_size
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T04:00:53.951105+00:00
-- url     : https://prove2.me/theorems/f81712a9-a85f-45f5-9a08-f3fe9452995c
-- title:
--   Proposition 16(c) — exact-one residue size bound
-- statement:
--   The exact-one functional residue system has at most $2m\sum_jp_j$ free and choice variables, while each of at most $\operatorname{gateBound}(a)$ gates contributes at most $66$ variables plus literal occurrences. Thus its variable count plus literal count is at most $2m\sum_jp_j+66\operatorname{gateBound}(a)$.
-- source:
--   Del Pia, STOC 2027 submission 398, Proposition 16(c), p.26: at most 18 variables per gate, at most 2-62+20+26=66 with literal-count bookkeeping, and 66r gates.

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Encoding

namespace ChvatalOneHard398.SAT

theorem proposition_16_exact_size (a : Params) (ha : a.Valid) :
    (functionalExact (residueSystem a).model).N +
      literalCount (functionalExact (residueSystem a).model) ≤
    2*a.m*a.p.sum + 66*gateBound a := by sorry
