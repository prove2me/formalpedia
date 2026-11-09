-- Prove2me | Theorems.Thm_ForgetAlt_mie_recompute
-- name    : ForgetAlt.mie_recompute
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:25:36.262436+00:00
-- url     : https://prove2.me/theorems/60c48268-be75-41ec-a3ff-110ed6b43a3d
-- title:
--   §5.1: MIEs of any ABT identified in $O(m\log n)$ time
-- statement:
--   Given $(G,M)$, the parity distances, and an arbitrary ABT $T$ (for instance one built by choosing parents along given double paths and arbitrarily elsewhere), an MIE $e^*_T(v)$ of every subtree $T(v)$ with $\tilde E_T(v)\ne\emptyset$ can be identified in $O(m'\log n')$ time, oriented with its inner endpoint in $T(v)$, by processing the non-tree edges in increasing order of level with upward walks and contraction.
--
--   This is the step that lets Theorem 1.1 use an arbitrary double-path algorithm, whose output need not respect the tree $T_0$ of ComputeDist.
--
--   Differences from the source:
--   - reading: its MIEs are identified in O(m log n) time → there is one program of the published word RAM EndStatement (constants b, C) whose step count on the stated input layout is at most C·(bound + 1), at every word width W ≥ b·(⌊log₂ size⌋ + 1); reason: the paper's time bounds are word-RAM bounds with O(log n)-bit words; the + 1 only matters when the bound is 0
--   - reading: “its MIEs are identified” → an MIE for every vertex v whose subtree has an incoming edge; reason: these are all the MIEs of T
--   - encoding: n and m → the extended counts n′ = n + |U| + 1, m′ = m + 2|U|; reason: Section 3.6 (p.28): “we also denote by n and m the numbers of vertices and edges of the extended system”
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Section 5.1, proof of Theorem 5.1, printed p.48 (PDF p.49)

import Mathlib
import Definitions.Def_ForgetAlt_Layouts
import Definitions.Def_ForgetAlt_ABT

namespace ForgetAlt

open BergeMatching.Core

/-- **Section 5.1, proof of Theorem 5.1**, printed p.48 (PDF p.49), unnumbered claim. Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…).

"… an ABT respecting the double paths is constructed by choosing the parents along the double
paths and arbitrarily elsewhere, and its MIEs are identified in `O(m log n)` time by processing
the non-tree edges in increasing order of level with the upward walks and the contraction of the
second part of ComputeDist, as in Section 3.6.2."

**Formalization Note.** One word-RAM program for all inputs: it reads `(G, M)`, the distance
arrays and the parent array of **any** ABT `T`, and outputs for every extended vertex index `i`
whose subtree `T(v)` has an incoming edge an MIE `{y, z}` of `T(v)`, oriented with
`z ∈ V(T(v))`, within `C·(m′·⌊log₂ n′⌋ + 1)` steps (`n′, m′` the extended counts, p.28). -/
theorem mie_recompute :
    ∃ (prog : List EndStatement.Instr) (b C : ℕ), ∀ (n : ℕ) (x : AugInstance n), x.Valid →
      ∀ par : ExtV (Fin n) → ExtV (Fin n), IsABT x.graph x.matching par →
      ∀ W : ℕ, b * (Nat.log2 (augSize x) + 1) ≤ W →
        ∃ t ≤ C * (extM x * Nat.log 2 (extN x) + 1),
          RunOutputs prog W t n (augInput x ++ distArrays x.graph x.matching ++ parArray par)
            (fun out => ∀ i : Fin (2 * n + 1),
              (∃ e, IsIncoming x.graph x.matching par (extOfIdx i) e) →
              ∃ y z : ExtV (Fin n), out (2 * i) = extIdx y ∧ out (2 * i + 1) = extIdx z ∧
                IsMIE x.graph x.matching par (extOfIdx i) s(y, z) ∧
                InSubtree x.graph x.matching par (extOfIdx i) z ∧
                ¬ InSubtree x.graph x.matching par (extOfIdx i) y) := by sorry

end ForgetAlt
