-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_latticeFormula_satisfiable_iff_candidates
-- name    : ChvatalOneHard398.SAT.latticeFormula_satisfiable_iff_candidates
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:48:37.473272+00:00
-- url     : https://prove2.me/theorems/0247d719-14d5-4610-9981-3ae05b68c415
-- title:
--   Proposition 16(a) as a satisfiability criterion
-- statement:
--   Let $a=(p,h,H,D,t)$ be valid residue parameters. Proposition 16(a), expressed directly as a satisfiability criterion, says that $F(p,h,H,D,t)$ is satisfiable exactly when there is an integer vector $y$ in the congruence kernel $\Lambda_D^\perp(H)$ whose displacement from $t$ lies in the asymmetric box:
--
--   $$
--   \exists y\in\Lambda_D^\perp(H),\qquad
--   -\bigl(2^{h-1}-1\bigr)\le t_i-y_i\le 2^{h-1}\quad\text{for every coordinate }i.
--   $$
--
--   This is the existential form used by the adaptive queries in Theorem 26. It avoids passing explicitly through Boolean assignments when proving that a bit-recovery query distinguishes two residue classes.
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.18 Proposition 16(a), applied on pp.27–29 in the proof of Theorem 26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Encoding

open scoped BigOperators

theorem ChvatalOneHard398.SAT.latticeFormula_satisfiable_iff_candidates
    (a : ChvatalOneHard398.SAT.Params) (ha : a.Valid) :
    ChvatalOneHard398.SAT.Satisfiable (ChvatalOneHard398.SAT.latticeFormula a) ↔
      ∃ y : Fin a.m → ℤ, y ∈ ChvatalOneHard398.SAT.congruenceKernel a.D a.H ∧
        ∀ i, -((2 : ℤ)^(a.h-1)-1) ≤ a.t i-y i ∧
          a.t i-y i ≤ (2 : ℤ)^(a.h-1) := by sorry
