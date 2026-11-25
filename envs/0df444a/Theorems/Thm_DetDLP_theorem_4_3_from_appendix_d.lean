-- Prove2me | Theorems.Thm_DetDLP_theorem_4_3_from_appendix_d
-- name    : DetDLP.theorem_4_3_from_appendix_d
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T05:00:22.827938+00:00
-- url     : https://prove2.me/theorems/e42e2812-6311-4551-8c39-6a3d880cf5be
-- title:
--   Terminal-preserving contraction under Appendix D.4
-- statement:
--   Assume the two interfaces of Appendix D.4. Let $b\ge2$ and $m,k\ge1$, with $m$ within a factor $C$ of the prescribed block count, $4mk$ within a factor $C$ of $b$, and $S\le Cmb$. Consider a bipartite tensor network with the prescribed lookup separator of degree bound $C\lceil b^{3/4}\rceil$, precision between $1$ and $S$, and truncation length between $1$ and $Cm$. Write $n=S+|\mathrm{desc}|$. Suppose the network has at most $(n+1)^{c_0}$ vertices and its entries are evaluable in polynomial time and space with the stipulated bound. A fixed machine takes the encoded instance, including the lookup vertices, and returns the canonical encoding of the full contraction in polynomial space and time
--   $$ (n+1)^{O(1)}2^{O(b/\sqrt{\log\log b})}.$$
--   The lookup vertices are part of the input; the output is the contracted scalar, not a table indexed by terminal assignments.
-- source:
--   Liu, Zhang, Ren (2026), Theorem 4.3; conditional on OpenAI (Oct 25, 2026), The Exponential Time Hypothesis is False, Appendix D, Section D.4, pp. 57–64.

import Mathlib
import Definitions.Def_DetDLP_OpenAIAppendixD
import Definitions.Def_DetDLP_FactorBase
import Definitions.Def_DetDLP_TerminalBTN

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

theorem theorem_4_3_from_appendix_d (hOAI : OpenAIAppendixDPremise) :
    ∀ (C c0 : ℕ), 0 < C → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (b m k S P0 ℓ : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P0 ℓ),
            2 ≤ b →
            1 ≤ m → 1 ≤ k →
            blockCount b ≤ C * m → m ≤ C * blockCount b →
            S ≤ C * m * b →
            4 * m * k ≤ C * b → b ≤ C * (4 * m * k) →
            1 ≤ P0 → P0 ≤ S →
            1 ≤ ℓ → ℓ ≤ C * m →
            G.nV ≤ (S + desc.length + 1) ^ c0 →
            ∀ (spec : LookupSeparatorSpec G m k S (C * Nat.ceil ((b : ℝ) ^ ((3 : ℝ) / 4)))),
            BTNEntryEvaluable desc G P0 ℓ T E outE
              (polyBound c0 (S + desc.length)) (polyBound c0 (S + desc.length)) →
            ∃ w : List Bool,
              EncodesTruncPoly P0 ℓ w (BTNContract G T) ∧
              RunsWithin M outM (encodeTerminalBTNInstance desc G b m k S P0 ℓ spec.lookupVerts) w
                (polyBound K (S + desc.length) * mainTimeBound K b)
                (polyBound K (S + desc.length)) := by sorry

end DetDLP
