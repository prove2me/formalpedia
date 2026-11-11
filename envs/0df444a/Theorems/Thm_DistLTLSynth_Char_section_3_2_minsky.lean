-- Prove2me | Theorems.Thm_DistLTLSynth_Char_section_3_2_minsky
-- name    : DistLTLSynth.Char.section_3_2_minsky
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:15:40.568569+00:00
-- url     : https://prove2.me/theorems/735e3421-5070-49c5-9924-ab1be7bb3ae7
-- title:
--   §3.2 (Minsky) — halting is undecidable for 2-counter machines
-- statement:
--   The set of (codes of) 2-counter machines $M=(Q,\Delta,q_{\mathrm{init}},F)$ whose run from $(q_{\mathrm{init}},0,0)$ reaches a halting state is not computable:
--   $$\{M \mid M \text{ halts}\}\ \text{is undecidable}.$$
--   This is the cited result [Min67] from which the undecidability direction of Theorem 1.2 reduces.
--
--   Differences from the source:
--   - encoding: 2-counter machines as inputs of a decision problem → CMCode = (s, q₀, F, Δ) with states Fin (s+1); out-of-range numbers read modulo, missing instructions read as a default increment; reason: every finite 2-counter machine is, up to renaming its states, described by a code, and decoding is primitive recursive
--   - encoding: undecidable → ¬ ComputablePred; reason: Mathlib's notion
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), p. 8 (PDF 9), §3.2 (citing [Min67, p. 255–258])

import Mathlib
import Definitions.Def_DistLTLSynth_Char_CounterMachine

namespace DistLTLSynth.Char

/-- §3.2 ([Min67]): halting (from the zero configuration) is undecidable for 2-counter
machines, given by their finite descriptions. -/
theorem section_3_2_minsky :
    ¬ ComputablePred (fun c : CMCode => (c.toMachine 2 (by norm_num)).Halts) := by sorry

end DistLTLSynth.Char
