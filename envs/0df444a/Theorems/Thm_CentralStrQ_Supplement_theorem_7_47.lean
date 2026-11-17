-- Prove2me | Theorems.Thm_CentralStrQ_Supplement_theorem_7_47
-- name    : CentralStrQ.Supplement.theorem_7_47
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:53:05.715093+00:00
-- url     : https://prove2.me/theorems/79102738-a7f6-4a97-89a3-d71f399924ea
-- title:
--   Theorem 7.47 — static cell-probe, Θ(log N)-bit cells: LCP and SA structures convert with O(S + N log σ) bits and O(Q+1) probes
-- statement:
--   Let $\sigma,N\ge2$ with $\sigma\le N$. Consider indexing for LCP queries and indexing for suffix array queries on the texts $T\in[0\,.\,.\,\sigma)^n$ with $\sigma\le n\le N$. In the static cell-probe model with $\Theta(\log N)$-bit cells, a deterministic data structure for either problem that supports every such text using $S(\sigma,N)$ bits of space and $Q(\sigma,N)$ probes per query yields a deterministic data structure for the other problem, on the same family of texts, with
--
--   $$O(S(\sigma,N)+N\log\sigma)\text{ bits of space and } O(Q(\sigma,N)+1)\text{ probes per query.}$$
--
--   This transfers cell-probe lower bounds for suffix array queries (Theorem 7.48, [KK27]) to LCP queries; Theorem 7.49 is the consequence.
--
--   **Formalization Note** A cell-probe structure has $M$ cells of $b$ bits filled by unrestricted preprocessing and, for each query, an adaptive decision tree of probes; space is $Mb$ bits and the cost is the number of probes on the followed path. Both directions use the same cell size $b$.
--
--   Differences from the source:
--   - encoding: static cell-probe model → CellProbeDS: M cells of b bits (zero beyond M), unrestricted preprocessing, an adaptive probing tree per query, space M·b bits, cost = probes on the followed path; reason: the standard model, made explicit
--   - reading: Θ(log N)-bit cells → a·log₂ N ≤ b ≤ a'·log₂ N with 0 < a ≤ a' quantified first; the new structure uses the same b; reason: the Θ-constants are fixed before the conclusion constant C
--   - encoding: O(·) bounds → one constant C > 0 depending only on a, a', chosen before σ, N, b, the given structure and its bounds; reason: the constants hidden in the O-notation are uniform
-- source:
--   Kempa–Kociumaka, A Complete Characterization of Central String Queries in Compact Space, STOC 2027 submission (manuscript sha256 dea2f74f66f1bd686c8e3c6d4e11f36643253c3c86a04fc5faa1c3ac1c96f346), Theorem 7.47, p.143 (pdf p.144)

import Mathlib
import Definitions.Def_CentralStrQ_Strings
import Definitions.Def_ConstTimeISA_Main_Prefix
import Definitions.Def_CentralStrQ_Supplement_CellProbe

set_option autoImplicit false

namespace CentralStrQ.Supplement

open CentralStrQ ConstTimeISA.Main

/-- Kempa–Kociumaka, *A Complete Characterization of Central String Queries in Compact Space*, STOC 2027 submission (manuscript sha256 dea2f74f…c96f346), Theorem 7.47, p.143 (PDF p.144): "Let σ, N ∈Z≥2 satisfy σ ≤N. Consider indexing for LCP queries (Definition 3.13) and indexing for suffix array queries (Definition 3.11) on texts T ∈[0 . . σ)n with σ ≤n ≤N. In the static cell-probe model with Θ(log N)- bit cells, a deterministic data structure for either problem that supports every such text using S(σ, N) bits of space and Q(σ, N) probes per query yields a deterministic data structure for the other problem, on the same family of texts, with the following bounds: • space usage O(S(σ, N) + N log σ) bits, • query time O(Q(σ, N) + 1) probes."

**Formalization Note.** Static cell-probe model as in `Def_CentralStrQ_Supplement_CellProbe` (unrestricted preprocessing, adaptive probes, space = cells × cell size). "Θ(log N)-bit cells" is `a·log₂ N ≤ b ≤ a'·log₂ N` with `0 < a ≤ a'` quantified first; the `O(·)` constant `C` depends only on `a`, `a'` and comes before `σ`, `N`, `b`, the given structure and its bounds. The new structure uses the same cell size `b`. One structure serves every text `T ∈ [0..σ)ⁿ` with `σ ≤ n ≤ N`; a query is `i ∈ [1..|T|]`. Both directions are stated. -/
theorem theorem_7_47 :
    ∀ a a' : ℝ, 0 < a → a ≤ a' → ∃ C : ℝ, 0 < C ∧
      ∀ (σ N b : ℕ), 2 ≤ σ → σ ≤ N → a * Real.logb 2 N ≤ b → (b : ℝ) ≤ a' * Real.logb 2 N →
        ∀ S t : ℝ,
          (CellProbeDS {T : List ℕ | σ ≤ T.length ∧ T.length ≤ N ∧ IsStr σ T}
              (fun T => {i : ℕ | 1 ≤ i ∧ i ≤ T.length}) (fun T i => LCP T i) b S t →
            CellProbeDS {T : List ℕ | σ ≤ T.length ∧ T.length ≤ N ∧ IsStr σ T}
              (fun T => {i : ℕ | 1 ≤ i ∧ i ≤ T.length}) (fun T i => SA T i) b
              (C * (S + N * Real.logb 2 σ)) (C * (t + 1))) ∧
          (CellProbeDS {T : List ℕ | σ ≤ T.length ∧ T.length ≤ N ∧ IsStr σ T}
              (fun T => {i : ℕ | 1 ≤ i ∧ i ≤ T.length}) (fun T i => SA T i) b S t →
            CellProbeDS {T : List ℕ | σ ≤ T.length ∧ T.length ≤ N ∧ IsStr σ T}
              (fun T => {i : ℕ | 1 ≤ i ∧ i ≤ T.length}) (fun T i => LCP T i) b
              (C * (S + N * Real.logb 2 σ)) (C * (t + 1))) := by sorry

end CentralStrQ.Supplement
