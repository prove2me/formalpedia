-- Prove2me | Theorems.Thm_DisjointPathsDAG_proposition_4_6
-- name    : DisjointPathsDAG.proposition_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:34:56.663009+00:00
-- url     : https://prove2.me/theorems/f99bca9f-23e8-439b-88a6-da1bc754b29d
-- title:
--   Proposition 4.6 (Reporting)
-- statement:
--   Fix $k\ge3$. In the setting of Theorem 4.1 over a finite field $F$ with $|F|\ge2k$:
--
--   1. there is a randomized algorithm (one machine program for all fields) that returns either "no" or a solution; it never returns an invalid tuple, always returns "no" when no solution exists, returns a solution with probability at least $1-n/|F|$ otherwise, and has expected running time $O_k(mn^{k-2}+n^k)$;
--   2. for every $\alpha>2$ and every generator $\mathrm{gen}$ of multiplication programs, there is a randomized algorithm with the same guarantees and expected running time $O_k(m+n^{k-3+\alpha})$ over every finite field with $|F|\ge2k$ over which $\mathrm{gen}$ multiplies $h\times h$ matrices as an identity of formal polynomials with $O(h^\alpha)$ operations, by programs constructible in linear time.
--
--   The constants depend on $k$ and on the hypothesis's constants, not on $F$. This turns the detection test into a reporting algorithm at the same cost.
--
--   Differences from the source:
--   - reading: "under the hypothesis of Proposition 4.4" → `MMSpecFormal` (the product as an identity of formal polynomials); reason: Section 4.5, p.20, assumes this explicitly
--   - generalization: an algorithm for a given field $F$ → one program and constants for every finite field with $|F|\ge2k$; reason: specializes to the source
--   - encoding: unit-cost field operations and sampling → the field bank of the machine; constants of the multiplication programs named by `fieldTable F`; reason: the machine of Section 2.1
--   - encoding: a DAG with a given topological order → the vertex numbering is the order (`IsTopo`: tail < head); reason: every DAG has one
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Proposition 4.6 (Reporting), p.20; Section 4.5, p.20

import Mathlib
import Definitions.Def_DisjointPathsDAG_Encoding
import Definitions.Def_DisjointPathsDAG_MMHyp

set_option autoImplicit false

namespace DisjointPathsDAG

/-- Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Proposition 4.6 (Reporting), p.20: "In the
setting of Theorem 4.1 over a field F with |F| ≥ 2k, there is a randomized algorithm that returns either
no or a solution. It never returns an invalid tuple, always returns no when no solution exists, and
returns a solution with probability at least 1 − n/|F| otherwise. Its expected running time is
Ok(mnk−2 + nk); under the hypothesis of Proposition 4.4, it is Ok(m + nk−3+α)."

For every `k ≥ 3`:
1. there are `C`, `A` and one machine program such that, over every finite field `F` with `|F| ≥ 2k`
   (the field bank) and on every instance of the setting of Theorem 4.1 (vertices numbered in a
   topological order; word width `A · ⌈log₂(N + 2)⌉` for the input size `N`): the expected running time is
   at most `C · (m n^(k−2) + n^k)`; every halting run outputs "no" or a solution (pairwise vertex-disjoint
   `sᵢ`–`tᵢ` paths in `Hᵢ`); it outputs "no" whenever no solution exists; and it outputs a solution with
   probability at least `1 − n/|F|` when one exists;
2. for every `α > 2` and every multiplication generator `gen` (constants `A'`, `C'`) there are `C`, `A`
   and one machine program with the same guarantees and expected running time at most
   `C · (m + n^(k−3+α))`, over every finite field `F` with `|F| ≥ 2k` over which `gen` multiplies
   `h × h` matrices as an identity of formal polynomials (`MMSpecFormal`, constants `fieldTable F`), with
   programs of size `≤ C' h^α` constructed in linear time.

**Formalization Note** "Under the hypothesis of Proposition 4.4" includes, by Section 4.5 (p.20), that
the multiplication program computes the product as an identity of formal polynomials; that is
`MMSpecFormal`. Its constants are named by `fieldTable F` (`0`, `1`, and every element of `F` through
`fofword`), the constants a machine program can produce at unit cost. The constants `C`, `A` and the
program do not depend on `F`. -/
theorem proposition_4_6 :
    ∀ k : ℕ, 3 ≤ k →
      (∃ (C : ℝ) (A : ℕ) (Prog : Program), 0 < C ∧ 1 ≤ A ∧
        ∀ (F : Type) [Field F] [Finite F], 2 * k ≤ Nat.card F →
        ∀ (n m : ℕ) (S : Setting n m k), S.G.IsTopo →
          ReportsWithin k Prog (wordWidth A (Input.size (⟨encodeInst S, [], []⟩ : Input F))) F
            ⟨encodeInst S, [], []⟩ (C * ((m : ℝ) * (n : ℝ) ^ (k - 2) + (n : ℝ) ^ k))
            (liftSol (S.G.IsSolutionIn S.H S.pairs)) (S.G.HasSolution S.H S.pairs)
            (1 - (n : ℝ) / Nat.card F)) ∧
      (∀ α : ℝ, 2 < α → ∀ (gen : Program) (A' : ℕ) (C' : ℝ),
        ∃ (C : ℝ) (A : ℕ) (Prog : Program), 0 < C ∧ 1 ≤ A ∧
          ∀ (F : Type) [Field F] [Finite F], 2 * k ≤ Nat.card F →
          MMSpecFormal F α (fieldTable F) gen A' C' →
          ∀ (n m : ℕ) (S : Setting n m k), S.G.IsTopo →
            ReportsWithin k Prog (wordWidth A (Input.size (⟨encodeInst S, [], []⟩ : Input F))) F
              ⟨encodeInst S, [], []⟩ (C * ((m : ℝ) + (n : ℝ) ^ ((k : ℝ) - 3 + α)))
              (liftSol (S.G.IsSolutionIn S.H S.pairs)) (S.G.HasSolution S.H S.pairs)
              (1 - (n : ℝ) / Nat.card F)) := by sorry

end DisjointPathsDAG
