-- Prove2me | Theorems.Thm_ConstrainedDirSep_STSep_theorem_5_2
-- name    : ConstrainedDirSep.STSep.theorem_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:09:16.744495+00:00
-- url     : https://prove2.me/theorems/2b0373b5-4c9e-4b55-b617-b4fb77bc62d1
-- title:
--   Theorem 5.2 — representation theorem: an FPT family of ordered representations, sound, complete, with staircase windows and chains
-- statement:
--   There are a constant $C$ and a deterministic multi-stack Turing machine $M$ such that for every loopless digraph $D$ on $n$ vertices, distinct terminals $s,t$, allowed set $\Lambda\subseteq V(D)\setminus\{s,t\}$ and integer $k\ge0$, $M$ halts on input $(D,s,t,\Lambda,k)$ within $C\cdot2^{C k^4\log k}\cdot(n+1)^C$ steps and outputs a family $\mathcal R$ of
--   $$|\mathcal R|\le C\cdot2^{Ck^4\log k}\cdot(\log n)^{Ck^3}$$
--   ordered representations of $D$, each of rank at most $k$, every domain nonempty ($d_i\ge1$), and of size at most $C(n+1)^C$, such that
--
--   - **(R1) Soundness.** For every $\rho\in\mathcal R$ and every feasible assignment $x$ of $\rho$, $S(x)$ is an $s$–$t$ separator of $D$ contained in $\Lambda$.
--   - **(R2) Completeness.** For every inclusion-minimal $s$–$t$ separator $S\subseteq\Lambda$ with $|S|\le k$, some $\rho\in\mathcal R$ represents $S$.
--   - **(R3) Window shape and closure.** Every window $W_{ij}$ ($i<j$) is a staircase $\{(p,q): L(p)\le q\le U(p)\}$ with $L,U$ nondecreasing, and is closed under coordinatewise minimum and maximum.
--   - **(R4) Chains.** For every $i<j$, both $F_{ij}\cap W_{ij}$ and $B_{ij}\cap W_{ij}$ are increasing chains.
--
--   Here $\log x=\log_2\max\{x,2\}$. Theorem 1.1 runs the Chain CSP algorithm on every representation of this family.
--
--   Differences from the source:
--   - reading: "of size polynomial in n with exponent independent of k" → every representation's encoding has length at most C·(n + 1)^C with the same universal C; reason: the stronger reading (no factor depending on k); the proof's representations have at most n candidates and O(n²) constraint bits per pair.
--   - reading: unnamed machine model → a deterministic Mathlib multi-stack Turing machine (TM2); reason: the bounds are polynomial in n for fixed k, the same in all polynomially equivalent deterministic models.
--   - encoding: 2^{O(k⁴ log k)} n^{O(1)} and 2^{O(k⁴ log k)}(log n)^{O(k³)} → C·2^{C·k⁴·⌊log₂ max(k, 2)⌋}·(n + 1)^C and C·2^{C·k⁴·⌊log₂ max(k, 2)⌋}·⌊log₂ max(n, 2)⌋^{C·k³}; reason: floors change log₂ by a factor at most 2, absorbed in C.
--   - encoding: (R3) "W_ij is a staircase with L, U nondecreasing" → there exist L, U : ℕ → ℤ, monotone on [d_i], with W_ij = {(p, q) ∈ [d_i] × [d_j] : L(p) ≤ q ≤ U(p)}; reason: Lean convention; same property.
--   - encoding: the family R → a list of representations (repetitions allowed) written as one output word; reason: a bound on the list length bounds the family's size.
-- source:
--   Olkowski, Ramanujan, Constrained Directed Separation: Algorithms and Classifications, STOC 2027 submission (manuscript sha256 4dd06c29…), pp. 18–19 (PDF 21–22), Theorem 5.2 (proof pp. 24–25, PDF 27–28)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_ConstrainedDirSep_STSep_Separator
import Definitions.Def_ConstrainedDirSep_STSep_Encoding
import Definitions.Def_ConstrainedDirSep_STSep_Quadrant
import Definitions.Def_ConstrainedDirSep_STSep_ChainCSP
import Definitions.Def_ConstrainedDirSep_STSep_OrderedRep

namespace ConstrainedDirSep.STSep

/-- Olkowski, Ramanujan, *Constrained Directed Separation*, STOC 2027 submission (manuscript
sha256 4dd06c29…), pp. 18–19 (PDF 21–22), Theorem 5.2 (Representation theorem): given `D` on `n`
vertices, distinct terminals `s`, `t`, an allowed set `Λ ⊆ V(D) \ {s, t}` and `k ≥ 0`, one computes
in time `2^{O(k⁴ log k)} n^{O(1)}` a family `R` of `2^{O(k⁴ log k)} (log n)^{O(k³)}` ordered
representations, each of rank at most `k`, with every domain nonempty and of size polynomial in
`n`, satisfying (R1) soundness, (R2) completeness, (R3) staircase min–max closed windows and (R4)
chains. `log x` is `log₂ max{x, 2}`. -/
theorem theorem_5_2 :
    ∃ C : ℕ, ∃ M : Turing.TM2ComputableAux Bool Bool,
      ∀ (n : ℕ) (D : Digraph (Fin n)), Loopless D → ∀ s t : Fin n, s ≠ t →
      ∀ Λ : Finset (Fin n), s ∉ Λ → t ∉ Λ → ∀ k : ℕ,
      ∃ R : List (OrderedRep n),
        HMBinPacking.OutputsWithin M (encRepInput D s t Λ k) (encRepFamily R)
          (C * 2 ^ (C * k ^ 4 * Nat.log 2 (max k 2)) * (n + 1) ^ C) ∧
        R.length ≤ C * 2 ^ (C * k ^ 4 * Nat.log 2 (max k 2)) * (Nat.log 2 (max n 2)) ^ (C * k ^ 3) ∧
        (∀ ρ ∈ R,
          ρ.WF s t ∧ ρ.lam ≤ k ∧ (∀ i, 1 ≤ ρ.d i) ∧ (encRep ρ).length ≤ C * (n + 1) ^ C ∧
          -- (R1) Soundness
          (∀ x : Fin ρ.lam → ℕ, ρ.Feasible x →
            IsSTSeparator D s t (ρ.selected x : Set (Fin n)) ∧ ρ.selected x ⊆ Λ) ∧
          -- (R3) Window shape and closure
          (∀ i j : Fin ρ.lam, i < j →
            (∃ L U : ℕ → ℤ, MonotoneOn L (Set.Icc 1 (ρ.d i)) ∧ MonotoneOn U (Set.Icc 1 (ρ.d i)) ∧
              ∀ p q : ℕ, 1 ≤ p → p ≤ ρ.d i → 1 ≤ q → q ≤ ρ.d j →
                ((p, q) ∈ ρ.W i j ↔ L p ≤ (q : ℤ) ∧ (q : ℤ) ≤ U p)) ∧
            MinMaxClosed (ρ.W i j)) ∧
          -- (R4) Chains
          (∀ i j : Fin ρ.lam, i < j →
            IsIncreasingChain (ρ.Fwd D i j ∩ ρ.W i j) ∧ IsIncreasingChain (ρ.Bwd D i j ∩ ρ.W i j))) ∧
        -- (R2) Completeness
        (∀ S : Finset (Fin n), S ⊆ Λ → IsMinimalSTSeparator D s t (S : Set (Fin n)) →
          S.card ≤ k → ∃ ρ ∈ R, ρ.Represents S) := by sorry

end ConstrainedDirSep.STSep
