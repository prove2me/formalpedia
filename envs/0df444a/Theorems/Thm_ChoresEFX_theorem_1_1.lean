-- Prove2me | Theorems.Thm_ChoresEFX_theorem_1_1
-- name    : ChoresEFX.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:06:14.450482+00:00
-- url     : https://prove2.me/theorems/b2ad905c-3264-4437-aedd-361b88fb708b
-- title:
--   Theorem 1.1 — a complete $(3+\varepsilon)$-EFX allocation in time polynomial in $n$, $m$, $L_c$ and $1/\varepsilon$
-- statement:
--   There are one multi-stack Turing machine $M$ and one polynomial $P$ such that the following holds for every instance with $n\ge1$ agents, $m$ chores and nonnegative rational costs, and every rational $0<\varepsilon\le1$. On the encoded input, $M$ halts within
--
--   $$P\big(n+m+|\mathrm{enc}(I,\varepsilon)|+\lceil1/\varepsilon\rceil\big)$$
--
--   steps with the encoding of a complete allocation $\sigma$ that is $(3+\varepsilon)$-EFX for the original costs: for all agents $i,j$ and every chore $g\in X_i$,
--
--   $$c_i(X_i\setminus\{g\})\le(3+\varepsilon)\,c_i(X_j).$$
--
--   The term $L_c$, the total binary encoding length of the cost matrix, is at most $|\mathrm{enc}(I,\varepsilon)|$.
--
--   The theorem replaces the previous polynomial-time factor $3n^2-n$ by a constant.
--
--   **Formalization Note** The machine and the polynomial are fixed before the instance and $\varepsilon$. The output word is an injective encoding of $\sigma$, so the machine cannot print anything other than the allocation.
--
--   Differences from the source:
--   - reading: can be computed in time polynomial in n, m, L_c, and 1/ε → ∃ TM2 machine and ∃ polynomial P, with a run within P(n + m + |enc| + ⌈1/ε⌉) steps; reason: the paper names no machine (paper.md decisions 3-4); its bound is polynomial in 1/ε, so the ceiling term is what the theorem says
--   - encoding: agents N, chores M, costs in ℚ≥0, an allocation as a partition → Fin n, Fin m, self-delimiting binary rationals, the allocation as a list of owners; malformed encoded inputs may get any output; reason: a Lean convention; same instances
--   - generalization: n ≥ 2 (standing, p.5) → n ≥ 1; reason: the proof says the case n = 1 is immediate (p.19), and the statement specializes to n ≥ 2
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), Theorem 1.1, p.2

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_ChoresEFX_IsAlphaEFX
import Definitions.Def_ChoresEFX_Inst

namespace ChoresEFX

/-- **Theorem 1.1**, p.2.

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC 2027
submission (manuscript sha256 b26d14cf…).

For every rational `0 < ε ≤ 1`, a complete `(3 + ε)`-EFX allocation can be computed in time polynomial in `n`, `m`,
`L_c` and `1/ε`.

**Formalization Note.** One multi-stack Turing machine `M` and one polynomial `P`, fixed before the instance and `ε`.
On input `enc(I, ε)`, `M` halts with `enc(σ)` within `P(n + m + |enc(I, ε)| + ⌈1/ε⌉)` steps, and `σ` is
`(3 + ε)`-EFX for the original costs. `L_c ≤ |enc(I, ε)|`, and `⌈1/ε⌉` is needed because the paper's bound is
polynomial in `1/ε`, not in the bit length of `ε` (paper.md decisions 3–5). -/
theorem theorem_1_1 :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (P : Polynomial ℕ),
      ∀ (I : Inst) (ε : ℚ), I.WellFormed → 0 < ε → ε ≤ 1 →
        ∃ σ : Fin I.m → Fin I.n,
          IsAlphaEFX I.realCost (3 + (ε : ℝ)) σ ∧
          HMBinPacking.OutputsWithin M (encInput I ε) (encAlloc σ)
            (P.eval (I.n + I.m + (encInput I ε).length + ⌈(1 / ε : ℚ)⌉₊)) := by sorry

end ChoresEFX
