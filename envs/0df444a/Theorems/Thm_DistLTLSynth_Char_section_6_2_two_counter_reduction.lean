-- Prove2me | Theorems.Thm_DistLTLSynth_Char_section_6_2_two_counter_reduction
-- name    : DistLTLSynth.Char.section_6_2_two_counter_reduction
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:17:17.852954+00:00
-- url     : https://prove2.me/theorems/5b783f2e-f8bb-4572-a8b2-3739f3716272
-- title:
--   §6.2, 2-counter reduction — a computable map M ↦ ϕ(M) to safety instances, realizable under Γ^ω iff M does not halt
-- statement:
--   For a 2-counter machine $M$, the paper applies the counter encoding to both counters, sharing the control state, and asserts that the resulting safety formula $\varphi(M)$ (singleton inputs, finite output sets) is realizable under $\Gamma^\omega$ iff $M$ does not halt, the map $M\mapsto\varphi(M)$ being computable:
--   $$\exists\ \text{computable } M\mapsto(\{\ast\},\{\ast\},Y_1^M,Y_2^M,\varphi(M)):\quad \varphi(M)\text{ safety and }\big(\varphi(M)\text{ realizable under }\Gamma^\omega\iff M\text{ does not halt}\big).$$
--   Together with Minsky's theorem this gives Theorem 1.1. (Finding I1: the 2-counter formula is never written and Theorem 6.12, invoked here, covers one counter only.)
--
--   Differences from the source:
--   - reading: 'apply the counter encoding to both counters … The resulting safety formula ϕ(M) is realizable under Γω iff M does not halt'; the 2-counter formula is never printed → there exists a computable map from 2-counter machine codes to instances with singleton input alphabets (k1 = k2 = 0), a safety formula, and realizability under Γ^ω iff non-halting; reason: this is exactly what §6.2 states and uses ('the map M ↦ ϕ̂(M) is computable'); no formula is printed to transcribe
--   - encoding: an instance consists of finite nonempty alphabets X_1, X_2, Y_1, Y_2 (with the interpretation of atomic propositions) and an LTL formula → Instance = (k1, k2, m1, m2, token list) with X_p = Fin (k_p+1), Y_p = Fin (m_p+1); the formula is a prefix-notation token list over ℕ-indexed atoms; an atom whose index is out of range is false, and a token list that is not exactly one formula is a no-instance; reason: a standard primitive-recursive encoding (Primcodable from ℕ, List and products through a computable, definitional equivalence); every paper instance has a code, and the two extra cases are decidable syntactic checks, so they change no decidability question
--   - encoding: 2-counter machines → CMCode decoded by toMachine 2; reason: as in the §3.2 item
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), p. 29 (PDF 30), §6.2; p. 8 (PDF 9), §3.2 ('the adaptation to a 2-counter machine is straightforward')

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL
import Definitions.Def_DistLTLSynth_Char_CounterMachine

namespace DistLTLSynth.Char

/-- §6.2, 2-counter reduction: a computable map `M ↦ ϕ(M)` sends every 2-counter machine to
an instance with singleton input sets and a safety formula that is realizable under `Γ^ω`
iff `M` does not halt. -/
theorem section_6_2_two_counter_reduction :
    ∃ red : CMCode → Instance, Computable red ∧
      ∀ c : CMCode, (red c).k1 = 0 ∧ (red c).k2 = 0 ∧ (red c).IsSafety ∧
        ((red c).Realizable Set.univ ↔ ¬ (c.toMachine 2 (by norm_num)).Halts) := by sorry

end DistLTLSynth.Char
