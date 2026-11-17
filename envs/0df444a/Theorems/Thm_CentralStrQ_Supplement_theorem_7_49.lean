-- Prove2me | Theorems.Thm_CentralStrQ_Supplement_theorem_7_49
-- name    : CentralStrQ.Supplement.theorem_7_49
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:53:30.454903+00:00
-- url     : https://prove2.me/theorems/81339486-7411-407b-b47f-688e07f3943d
-- title:
--   Theorem 7.49 — cell-probe lower bound: binary-text LCP structures with S(N) = Ω(N) bits need Ω(log log N / log((S/N) log log N)) query time
-- statement:
--   Let $N$ be a sufficiently large positive integer. In the cell-probe model with $\Theta(\log N)$-bit cells, every deterministic data structure supporting LCP queries for every binary text $T\in\{0,1\}^*$ with $2\le|T|\le N$, using at most $S(N)$ bits of space where $S(N)=\Omega(N)$, has worst-case query time
--
--   $$Q(N)=\Omega\Bigl(\frac{\log\log N}{\log\bigl((S(N)/N)\log\log N\bigr)}\Bigr).$$
--
--   Constant-time LCP queries are therefore impossible in $O(N)$ bits for binary texts in the cell-probe model, in contrast with PLCP queries (Theorem 10.2).
--
--   **Formalization Note** Same cell-probe model as Theorem 7.47. `log` is $\log_2$.
--
--   Differences from the source:
--   - encoding: static cell-probe model → CellProbeDS (as in Theorem 7.47); reason: the standard model, made explicit
--   - reading: N sufficiently large, Θ(log N)-bit cells, S(N) = Ω(N), Q(N) = Ω(…) → for all 0 < a ≤ a' (cells of b bits with a·log₂ N ≤ b ≤ a'·log₂ N) and every c_S > 0 there are c_Q > 0 and N₀ such that for N ≥ N₀ every structure with S ≥ c_S·N bits and at most t probes has t ≥ c_Q·log log N / log((S/N)·log log N); reason: the quantifier reading of the asymptotic notation; the denominator keeps its dependence on S
-- source:
--   Kempa–Kociumaka, A Complete Characterization of Central String Queries in Compact Space, STOC 2027 submission (manuscript sha256 dea2f74f66f1bd686c8e3c6d4e11f36643253c3c86a04fc5faa1c3ac1c96f346), Theorem 7.49, p.144 (pdf p.145)

import Mathlib
import Definitions.Def_CentralStrQ_Strings
import Definitions.Def_ConstTimeISA_Main_Prefix
import Definitions.Def_CentralStrQ_Supplement_CellProbe

set_option autoImplicit false

namespace CentralStrQ.Supplement

open CentralStrQ ConstTimeISA.Main

/-- Kempa–Kociumaka, *A Complete Characterization of Central String Queries in Compact Space*, STOC 2027 submission (manuscript sha256 dea2f74f…c96f346), Theorem 7.49, p.144 (PDF p.145): "Let N be a sufficiently large positive integer. In the cell-probe model with Θ(log N)- bit cells, every deterministic data structure supporting LCP queries (Definition 3.13) for every binary text T ∈{0, 1}∗satisfying 2 ≤|T| ≤N, using at most S(N) bits of space, where S(N) = Ω(N), has worst-case query time Q(N) = Ω (︃ log log N log((S(N)/N) log log N) )︃ ."

**Formalization Note.** Static cell-probe model as in `Def_CentralStrQ_Supplement_CellProbe`. "Θ(log N)-bit cells" is `a·log₂ N ≤ b ≤ a'·log₂ N` with `0 < a ≤ a'` quantified first; "S(N) = Ω(N)" is `S ≥ c_S·N` for a constant `c_S > 0` quantified next; "N sufficiently large" and "Q(N) = Ω(…)" are a constant `c_Q > 0` and a threshold `N₀`, depending only on `a`, `a'`, `c_S`. A structure using at most `S` bits with at most `t` probes per query has `t ≥ c_Q·log log N / log((S/N)·log log N)`; the denominator keeps its dependence on `S`. One structure serves every binary text with `2 ≤ |T| ≤ N`. `log` is `Real.logb 2`. -/
theorem theorem_7_49 :
    ∀ a a' : ℝ, 0 < a → a ≤ a' → ∀ cS : ℝ, 0 < cS →
      ∃ cQ : ℝ, 0 < cQ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ b : ℕ, a * Real.logb 2 N ≤ b → (b : ℝ) ≤ a' * Real.logb 2 N →
        ∀ S t : ℝ, cS * N ≤ S →
          CellProbeDS {T : List ℕ | 2 ≤ T.length ∧ T.length ≤ N ∧ IsStr 2 T}
            (fun T => {i : ℕ | 1 ≤ i ∧ i ≤ T.length}) (fun T i => LCP T i) b S t →
          cQ * (Real.logb 2 (Real.logb 2 N) / Real.logb 2 (S / N * Real.logb 2 (Real.logb 2 N))) ≤ t := by sorry

end CentralStrQ.Supplement
