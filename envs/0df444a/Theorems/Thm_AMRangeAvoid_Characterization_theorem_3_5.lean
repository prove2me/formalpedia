-- Prove2me | Theorems.Thm_AMRangeAvoid_Characterization_theorem_3_5
-- name    : AMRangeAvoid.Characterization.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:02:11.892197+00:00
-- url     : https://prove2.me/theorems/61a8d9f5-54a7-4e3c-a9fc-dc4520e8094b
-- title:
--   Theorem 3.5 — targeted hitting strings for the SSLB verifier reduce to Avoid
-- statement:
--   Fix the actual SSLB verifier from the proof of Theorem 3.3, with the same acceptance predicate as in the preceding milestone. Its targeted hitting-string search problem satisfies
--   $$\mathrm{THS}(\mathrm{SSLB},V_{\mathrm{SSLB}})\le_p\mathrm{Avoid}.$$
--   There exist two total deterministic polynomial-time algorithms: the first produces on every input an ordinary circuit with one more output than input; the second translates every correctly sized missing output, on every promised SSLB NO input, to one full challenge rejected for every full Merlin response. The translator always produces a challenge of the correct length. This establishes the forward reduction for the specified verifier, without assuming an algorithm for solving Avoid.
--
--   Differences from the source:
--   - encoding: ordinary binary strings, explicit Boolean circuits and deterministic polynomial-time algorithms → self-delimiting binary codes, ordinary topological multi-output circuits and actual polynomial-clock TM2 transducers; reason: standard binary representations with polynomial overhead; input arities and all output wires contribute to full code length
--   - encoding: the instance-dependent raw shifted-hash messages in the proof of Theorem 3.3 → the same raw protocol padded in both messages to p(L)=4000000(L+1)^12, with unused bits ignored; reason: raw lengths are bounded by p(L) for every active-branch valid code; padding preserves perfect completeness and the exact acceptance fraction and supplies the length-only interface of Definition 2.2
--   - encoding: the translator returns a candidate in the verifier random-string domain → the translator has the prescribed output length for every correctly sized Avoid candidate, including on YES inputs; reason: makes the source candidate type explicit, as required for the perfect-completeness step in Theorem 3.7; no rejection guarantee is imposed off the NO promise
-- source:
--   Zeyong Li, STOC 2027 submission #502 (October 2026), Theorem 3.5, printed p.16 (PDF p.18), proof through printed p.17 (PDF p.19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/502.pdf

import Definitions.Def_AMRangeAvoid_Characterization_Protocol

namespace AMRangeAvoid.Characterization

/-- Li, STOC 2027 submission #502, Theorem 3.5, printed pp.16–17 (PDF pp.18–19).
The source's actual verifier is fixed by its operational definition, rather than
being supplied with an assumed range-containment property.
-/
theorem theorem_3_5 : SearchReducesToAvoid (TargetedHitting SSLB sslbVerifier) := by sorry

end AMRangeAvoid.Characterization
