-- Prove2me | Theorems.Thm_AMRangeAvoid_Characterization_corollary_3_8
-- name    : AMRangeAvoid.Characterization.corollary_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:02:19.384403+00:00
-- url     : https://prove2.me/theorems/0e4a4bb9-6658-4e33-b6cf-3e78b8894a3c
-- title:
--   Corollary 3.8 — the full SSLB characterization
-- statement:
--   For every promise problem $\Pi\in\mathrm{prAM}_{1,1/3}$, the following statements are equivalent:
--   $$\Pi\le_p\mathrm{SSLB}\quad\Longleftrightarrow\quad\exists V\text{ witnessing }\Pi\in\mathrm{prAM}_{1,1/3},\quad\mathrm{THS}(\Pi,V)\le_p\mathrm{Avoid}.$$
--   All reductions are deterministic polynomial-time many-one reductions. The decision reduction preserves both promised sides, and the search reduction must translate every correctly sized Avoid solution on every promised NO input. The verifier on the right is existentially chosen; perfect completeness and soundness at most one third are retained. This characterizes exactly the stated fragment of promise Arthur–Merlin verification without assuming that Avoid is efficiently solvable.
--
--   Differences from the source:
--   - encoding: ordinary binary strings, explicit Boolean circuits and deterministic polynomial-time algorithms → self-delimiting binary codes, ordinary topological multi-output circuits and actual polynomial-clock TM2 transducers; reason: standard binary representations with polynomial overhead; input arities and all output wires contribute to full code length
--   - encoding: polynomial random/response lengths and probabilities on uniform finite binary words → natural-valued rational-coefficient polynomial lengths and exact integer challenge counts; reason: retains every natural-valued polynomial length without rounding and expresses soundness 1/3 by three times the answerable count at most the number of challenges
--   - encoding: the translator returns a candidate in the verifier random-string domain → the translator has the prescribed output length for every correctly sized Avoid candidate, including on YES inputs; reason: makes the source candidate type explicit, as required for the perfect-completeness step in Theorem 3.7; no rejection guarantee is imposed off the NO promise
-- source:
--   Zeyong Li, STOC 2027 submission #502 (October 2026), Corollary 3.8 (Equivalence), printed p.18 (PDF p.20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/502.pdf

import Definitions.Def_AMRangeAvoid_Characterization_Protocol

namespace AMRangeAvoid.Characterization

/-- Li, STOC 2027 submission #502, Corollary 3.8, printed p.18 (PDF p.20).
Full equivalence for all promise problems in prAM with perfect completeness
and soundness 1/3. Both reduction notions use actual uniform polynomial-time
machines, and the verifier on the right is existentially chosen.
-/
theorem corollary_3_8 (problem : PromiseProblem) (hAM : InPrAM problem) :
    PromiseReduces problem SSLB ↔
      ∃ V : AMVerifier, WitnessesAM problem V ∧
        SearchReducesToAvoid (TargetedHitting problem V) := by sorry

end AMRangeAvoid.Characterization
