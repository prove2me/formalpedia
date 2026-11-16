-- Prove2me | Theorems.Thm_AMRangeAvoid_Characterization_Supplement_theorem_5_1
-- name    : AMRangeAvoid.Characterization.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:30:08.974914+00:00
-- url     : https://prove2.me/theorems/d99f1a43-4421-42ca-936d-e87feb424c12
-- title:
--   Theorem 5.1 — SearchNP for a fixed Avoid family implies promise NP
-- statement:
--   Fix a promise problem $\Pi$, a verifier $V$ witnessing $\Pi\in\mathrm{prAM}_{1,1/3}$, and a particular deterministic polynomial-time targeted-hitting reduction $(f,g)$. The circuit $f(x)$ expands by one bit on every input, and $g$ has the verifier's challenge length on every input. If every input has an accepting nondeterministic polynomial-time branch producing a non-image of $f(x)$, and every accepting branch produces such a non-image, then
--
--   $$\mathrm{Avoid}_f\in\mathrm{SearchNP}\quad\Longrightarrow\quad\Pi\in\mathrm{prNP}.$$
--
--   The hypothesis is specific to $f$. Its totality includes YES and unpromised inputs; it does not assume a solver for arbitrary expanding circuits.
--
--   Differences from the source:
--   - encoding: a nondeterministic polynomial-time machine with totality and universal correctness of accepting paths → polynomial-length branch certificates, operational polynomial-time acceptance and output transducers, totality for every x, and correctness for every accepted certificate; reason: polynomially clocked nondeterministic paths and such certificates describe the same SearchNP class
-- source:
--   Zeyong Li, STOC 2027 submission #502 (October 2026), Theorem 5.1, printed p.24 (PDF p.26); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/502.pdf

import Definitions.Def_AMRangeAvoid_Characterization_Supplement_Complexity
import Definitions.Def_AMRangeAvoid_Characterization_SSLB

namespace AMRangeAvoid.Characterization.Supplement

theorem theorem_5_1 (A : PromiseProblem) (V : AMVerifier)
    (hV : WitnessesAM A V) (f : Bits → Bits) (g : Bits → Bits → Bits)
    (hfg : IsAvoidReduction (TargetedHitting A V) f g)
    (hSearch : InSearchNP (AvoidFamily f)) : InPrNP A := by sorry

end AMRangeAvoid.Characterization.Supplement
