-- Prove2me | Theorems.Thm_ForgetAlt_theorem_3_22
-- name    : ForgetAlt.theorem_3_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:27:40.74431+00:00
-- url     : https://prove2.me/theorems/f23e9ad7-596d-4ae6-b328-ff7186a12135
-- title:
--   Theorem 3.22: ComputeDist computes all parity distances and an ABT in $O(m\log n)$; the ABD, volumes and heights in $O(m+n)$ more
-- statement:
--   There is an algorithm that, given $(G,M)$, outputs $\mathrm{dist}^\theta(v)$ for every vertex $v$ of the extended system and both parities (including infinite values) and an ABT $T_0$, in time $O(m'\log n')$, where $n'=n+|U|+1$ and $m'=m+2|U|$ are the vertex and edge counts of the extended system. From these distances, the ABD and the volumes and heights of all edges are obtained in $O(m'+n')$ additional time.
--
--   Differences from the source:
--   - reading: the algorithm ComputeDist … runs in O(m log n) time; … in O(m + n) additional time → there is one program of the published word RAM EndStatement (constants b, C) whose step count on the stated input layout is at most C·(bound + 1), at every word width W ≥ b·(⌊log₂ size⌋ + 1); reason: the paper's time bounds are word-RAM bounds with O(log n)-bit words; the + 1 only matters when the bound is 0
--   - reading: the algorithm ComputeDist (Algorithm 2) has these properties → there is a word-RAM program with ComputeDist's input/output behaviour and time bound; reason: the claim's content used later is the input/output behaviour and the time; the program is ComputeDist's implementation
--   - encoding: the ABD and all edge volumes and heights → per input edge an arc code (1, 2, 0), its volume and height; per free u the volumes and heights of {f, a_u}, {a_u, u}; the arcs a_u → f and u → a_u are fixed by the construction; reason: output layout
--   - encoding: “additional time” after ComputeDist → a second program reading (G, M) and the distance arrays; reason: the distances are what ComputeDist leaves for this step
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Theorem 3.22, printed p.32 (PDF p.33)

import Mathlib
import Definitions.Def_ForgetAlt_Layouts
import Definitions.Def_ForgetAlt_ABT

namespace ForgetAlt

open BergeMatching.Core

/-- **Theorem 3.22**, printed p.32 (PDF p.33). Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…).

"The algorithm ComputeDist satisfies `Dist^θ[v] = dist^θ(v)` for all `v ∈ V(G)` and
`θ ∈ {odd, even}` at the end of the algorithm, including infinite values, and the chosen tree at
the end is an ABT `T₀`. It runs in `O(m log n)` time. The ABD and all edge volumes and heights
can then be obtained in `O(m + n)` additional time."

**Formalization Note.** Both parts are word-RAM programs (`EndStatement`) for all inputs, at every
width `W ≥ b·(⌊log₂(n + m + 2)⌋ + 1)`. `n, m` in the bounds are the counts of the extended system,
`n′ = n + |U| + 1` and `m′ = m + 2|U|` (p.28). Part 1 reads `(G, M)` and outputs, for every
extended vertex index `i`, the coded `dist^even`, `dist^odd` (`⊤ ↦ 0`, `d ↦ d + 1`, so `∞` is
exact) and a parent, the parents forming an ABT. Part 2 reads `(G, M)` and the distance arrays
and outputs, for the `j`-th input edge `{a, b}`, an arc code (`1`: `(a, b)` is an ABD arc, `2`:
`(b, a)` is, `0`: neither) with its volume and height, and for each free `u` the volumes and
heights of `{f, a_u}` and `{a_u, u}`. The remaining ABD arcs (`a_u → f`, `u → a_u`) are fixed by
the construction. -/
theorem theorem_3_22 :
    (∃ (prog : List EndStatement.Instr) (b C : ℕ), ∀ (n : ℕ) (x : AugInstance n), x.Valid →
      ∀ W : ℕ, b * (Nat.log2 (augSize x) + 1) ≤ W →
        ∃ t ≤ C * (extM x * Nat.log 2 (extN x) + 1),
          RunOutputs prog W t n (augInput x) (fun out =>
            (∀ i : Fin (2 * n + 1),
              out (3 * i) = enatCode (dist x.graph x.matching .even (extOfIdx i)) ∧
              out (3 * i + 1) = enatCode (dist x.graph x.matching .odd (extOfIdx i))) ∧
            ∃ par, IsABT x.graph x.matching par ∧ ∀ i : Fin (2 * n + 1), extOfIdx i ≠ .f →
              Reach x.graph x.matching (extOfIdx i) → out (3 * i + 2) = extIdx (par (extOfIdx i)))) ∧
    (∃ (prog : List EndStatement.Instr) (b C : ℕ), ∀ (n : ℕ) (x : AugInstance n), x.Valid →
      ∀ W : ℕ, b * (Nat.log2 (augSize x) + 1) ≤ W →
        ∃ t ≤ C * (extM x + extN x + 1),
          RunOutputs prog W t n (augInput x ++ distArrays x.graph x.matching) (fun out =>
            (∀ (j : ℕ) (e : Fin n × Fin n × Bool), x.edges[j]? = some e →
              ((out (3 * j) = 1 ↔ abdArc x.graph x.matching (.orig e.1) (.orig e.2.1)) ∧
               (out (3 * j) = 2 ↔ abdArc x.graph x.matching (.orig e.2.1) (.orig e.1)) ∧
               (out (3 * j) = 0 ↔ ¬ abdArc x.graph x.matching (.orig e.1) (.orig e.2.1) ∧
                  ¬ abdArc x.graph x.matching (.orig e.2.1) (.orig e.1))) ∧
              out (3 * j + 1) = enatCode (vlevelE x.graph x.matching s(.orig e.1, .orig e.2.1)) ∧
              out (3 * j + 2) = enatCode (hlevelE x.graph x.matching s(.orig e.1, .orig e.2.1))) ∧
            ∀ u : Fin n, IsNeutral x.matching u →
              out (3 * x.edges.length + 4 * u) = enatCode (vlevelE x.graph x.matching s(.f, .aux u)) ∧
              out (3 * x.edges.length + 4 * u + 1) =
                enatCode (hlevelE x.graph x.matching s(.f, .aux u)) ∧
              out (3 * x.edges.length + 4 * u + 2) =
                enatCode (vlevelE x.graph x.matching s(.aux u, .orig u)) ∧
              out (3 * x.edges.length + 4 * u + 3) =
                enatCode (hlevelE x.graph x.matching s(.aux u, .orig u)))) := by sorry

end ForgetAlt
