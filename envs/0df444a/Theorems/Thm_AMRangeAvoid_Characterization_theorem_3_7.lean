-- Prove2me | Theorems.Thm_AMRangeAvoid_Characterization_theorem_3_7
-- name    : AMRangeAvoid.Characterization.theorem_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:02:41.385227+00:00
-- url     : https://prove2.me/theorems/99d799d4-4682-457c-9755-5e4dad9a4bb1
-- title:
--   Theorem 3.7 — a targeted hitting reduction implies a reduction to SSLB
-- statement:
--   Let $\Pi$ be any promise problem, and fix any deterministic polynomial-time verifier $V$ witnessing $\Pi\in\mathrm{prAM}_{1,1/3}$. If the $V$-Targeted Hitting String problem has a deterministic polynomial-time many-one reduction to Avoid, then
--   $$\Pi\le_p\mathrm{SSLB}.$$
--   The conclusion is one total deterministic polynomial-time map taking all promised YES inputs to SSLB YES inputs and all promised NO inputs to SSLB NO inputs. The verifier is arbitrary subject to the original perfect-completeness and soundness conditions. This is the converse milestone for the complete characterization.
--
--   Differences from the source:
--   - encoding: ordinary binary strings, explicit Boolean circuits and deterministic polynomial-time algorithms → self-delimiting binary codes, ordinary topological multi-output circuits and actual polynomial-clock TM2 transducers; reason: standard binary representations with polynomial overhead; input arities and all output wires contribute to full code length
--   - encoding: polynomial random/response lengths and probabilities on uniform finite binary words → natural-valued rational-coefficient polynomial lengths and exact integer challenge counts; reason: retains every natural-valued polynomial length without rounding and expresses soundness 1/3 by three times the answerable count at most the number of challenges
--   - encoding: the translator returns a candidate in the verifier random-string domain → the translator has the prescribed output length for every correctly sized Avoid candidate, including on YES inputs; reason: makes the source candidate type explicit, as required for the perfect-completeness step in Theorem 3.7; no rejection guarantee is imposed off the NO promise
-- source:
--   Zeyong Li, STOC 2027 submission #502 (October 2026), Theorem 3.7, printed p.18 (PDF p.20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/502.pdf

import Definitions.Def_AMRangeAvoid_Characterization_Protocol

namespace AMRangeAvoid.Characterization

/-- Li, STOC 2027 submission #502, Theorem 3.7, printed p.18 (PDF p.20).
Every fixed qualifying verifier is covered, with the original promise problem.
-/
theorem theorem_3_7 (problem : PromiseProblem) (V : AMVerifier)
    (hV : WitnessesAM problem V)
    (hred : SearchReducesToAvoid (TargetedHitting problem V)) :
    PromiseReduces problem SSLB := by sorry

end AMRangeAvoid.Characterization
