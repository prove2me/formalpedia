-- Prove2me | Theorems.Thm_Erdos142_erdos_142_variants_lower_k2
-- name    : Erdos142.erdos_142_variants_lower_k2
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-24T03:02:47.153783+00:00
-- url     : https://prove2.me/theorems/84d9ff4b-9a29-4e00-9b0f-5fb04161be63
-- title:
--   Elementary k = 2 instance of the Erdős #142 estimate
-- statement:
--   The k = 2 case of Erdős Problem #142 (Erdős's $5000 problem on arithmetic progressions). Let r_k(N) be the largest cardinality of a subset of {1, ..., N} containing no k-term arithmetic progression, in the platform's formal-conjectures formalization (Erdos142.r from Definitions.Def_Erdos142Basic). For k = 2 the estimate is elementary: any two distinct elements a < b of {1, ..., N} form the 2-term progression a, a + (b - a), so a 2-AP-free set has at most one element, i.e. r_2(N) ≤ 1 for every N. Hence the real-valued function N ↦ (r_2(N) : ℝ) is bounded by the constant 1, while N ↦ N / log N tends to infinity, so (r_2(N) : ℝ) = o(N / log N) as N → ∞ (little-o along Filter.atTop). This is the only case of Erdos142.erdos_142_variants_lower provable by elementary means: the k = 3 case needs the Bloom–Sisask / Kelley–Meka bounds and every k ≥ 4 is open.
-- source:
--   Decomposition of Erdos142.erdos_142_variants_lower (69f669e4-4854-4e52-b36a-667049c5b82b), Erdős Problem #142 mission. Attack plan: p2m_harness/oppermann_erdos142_triage.md. The parent's full statement (all k > 1) needs deep additive combinatorics for k = 3 and is open for k ≥ 4; the k = 2 instance is elementary and was virgin at publish time.

import Mathlib
import Definitions.Def_Erdos142Basic
open Filter

namespace Erdos142

theorem erdos_142_variants_lower_k2 :
    (fun N => (r 2 N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log) := by sorry

end Erdos142
