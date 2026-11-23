-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_proposition_16_candidateEquiv
-- name    : ChvatalOneHard398.SAT.proposition_16_candidateEquiv
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:59:47.719304+00:00
-- url     : https://prove2.me/theorems/891b5d98-7f0e-48f9-8fad-996669902741
-- title:
--   Proposition 16(a) — residue and lattice candidate equivalence
-- statement:
--   After replacing $t$ by $t+(2^{h-1}-1)\mathbf1$, the residue candidates are in bijection with the lattice candidates. Concretely, $c=t-\tilde y+(2^{h-1}-1)\mathbf1$ with $\tilde y=Hy+bDz$, so the residue inequalities are exactly $\tilde y\in M$ and $t-\tilde y\in\mathcal B_h$.
-- source:
--   Del Pia, STOC 2027 submission 398, Proposition 16(a), p.26, second paragraph.

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Encoding

namespace ChvatalOneHard398.SAT

theorem proposition_16_candidateEquiv (a : Params) (ha : a.Valid) :
    Nonempty (residueCandidates
      {a with t := fun i => a.t i + ((2 : ℤ)^(a.h-1)-1)} ≃ candidateVectors a) := by sorry
