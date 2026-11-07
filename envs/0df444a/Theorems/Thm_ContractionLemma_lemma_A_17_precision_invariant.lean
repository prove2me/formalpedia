-- Prove2me | Theorems.Thm_ContractionLemma_lemma_A_17_precision_invariant
-- name    : ContractionLemma.lemma_A_17_precision_invariant
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:57:13.759548+00:00
-- url     : https://prove2.me/theorems/1233da3a-b09c-4077-8ee3-8ab67f52fc6c
-- title:
--   Lemma A.17 — precision invariant
-- statement:
--   There are $s^*$ and $c^*$ depending only on $C$ such that for $s\ge s^*$: in every call of the recursion at depth $d$ the incoming precision satisfies
--
--   $$
--   p\le 47Cs\,2^{a_{d-1}},
--   $$
--
--   and if moreover $M>H$, then $p_t\le c^*MD_i/u_d$ for every easy point $t$ of level $i<u_d$.
--
--   So the precision requested from the children stays within what Lemma A.15(c) can absorb.
--
--   **Formalization Note** A call is described by its root-to-call path: the top precision $P\le Cs$ and, for each ancestor at depth $j<d$, its edge count $H<M_j\le Cs8^{-j}$, the level $i_j<u_j$ of the easy point the path passes through, and the precision $p_{j+1}=p_j+8\lceil 3M_j/u_j\rceil2^{a_j-i_j}+8M_j(a_j+1)$.
--
--   Differences from the source:
--   - reading: in every call of the recursion at depth d → every path of edge counts, levels and precisions obeying the recursion rules; reason: these rules are what the proof uses about a call; any reachable call is such a path
--   - reading: c* depends only on C → ∃ c* before s, without the value 34 from the proof; reason: the printed statement does not give the value of c*
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Lemma A.17, p.76; proof pp.95–96

import Mathlib
import Definitions.Def_ContractionLemma_aSlot

set_option autoImplicit false

namespace ContractionLemma

/-- **Lemma A.17 (Precision invariant)** — Gajulapalli, *The Contraction Lemma Beyond ETH*
(manuscript, sha256 049caea1…), p.76 (PDF p.79); proof pp.95–96.

Let `s ≥ s*`. In every call of the recursion at depth `d`, the incoming precision satisfies
`p ≤ 47 C s 2^{a_{d−1}}`. If moreover `M > H`, then `p_t ≤ c* M D_i/u_d` for every easy point `t`
of level `i < u_d`, where `c*` depends only on `C`.

**Formalization Note.** A call at depth `d` is described by its root-to-call path: the top
precision `P ≤ C s`, and for each ancestor at depth `j < d` its edge count `M_j` with
`H < M_j ≤ C s 8^{−j}` (ancestors are internal calls), the level `i_j < u_j` of the easy point
through which the path passes, and the precision `p_{j+1} = p_j + 8⌈3M_j/u_j⌉ 2^{a_j − i_j} +
8M_j(a_j + 1)` it asks of its children (`childPrec`). The second claim is about the call itself,
with `H < M_d ≤ C s 8^{−d}`; `D_i = 2^{a_d − i}`. -/
theorem lemma_A_17_precision_invariant (C : ℝ) (hC : 0 < C) :
    ∃ (sStar : ℕ) (cStar : ℝ), ∀ s ≥ sStar, ∀ (d P : ℕ) (Ms is ps : ℕ → ℕ),
      (P : ℝ) ≤ C * s → ps 0 = P →
      (∀ j < d, leafH s < Ms j ∧ (Ms j : ℝ) ≤ C * s / 8 ^ j ∧ is j < uLev s j ∧
        ps (j + 1) = childPrec s j (Ms j) (is j) (ps j)) →
      (ps d : ℝ) ≤ 47 * C * s * 2 ^ aPrev s d ∧
      (leafH s < Ms d → (Ms d : ℝ) ≤ C * s / 8 ^ d → ∀ i < uLev s d,
        (childPrec s d (Ms d) i (ps d) : ℝ) ≤
          cStar * Ms d * 2 ^ (aSlot s d - i) / uLev s d) := by sorry

end ContractionLemma
