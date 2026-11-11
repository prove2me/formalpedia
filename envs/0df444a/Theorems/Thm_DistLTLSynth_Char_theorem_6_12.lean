-- Prove2me | Theorems.Thm_DistLTLSynth_Char_theorem_6_12
-- name    : DistLTLSynth.Char.theorem_6_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:18:14.082398+00:00
-- url     : https://prove2.me/theorems/d7234283-5815-478f-a455-ba530862f536
-- title:
--   Theorem 6.12 — a 1-counter machine does not halt iff ϕ(M_counter) is realizable
-- statement:
--   Let $M_{\mathrm{counter}}=(Q,\Delta,q_{\mathrm{init}},F,\{c_1\})$ be a 1-counter machine with finite $Q$. With singleton inputs and the output tuples $(q,\mathit{zero},\mathit{plan},\mathit{carry},\mathit{pos})$,
--   $$M_{\mathrm{counter}}\text{ does not halt}\iff \varphi(M_{\mathrm{counter}})\text{ is realizable (under }\Gamma^\omega),$$
--   with $\varphi(M_{\mathrm{counter}})$ the formula of Eq. (31). The view complex of a realizer stores the counter as the fraction $3^{-c}$ of weight-1 edges. Theorem 6.12 is stated for one counter; §6.2 applies the 2-counter version (see the §6.2 item).
--
--   Differences from the source:
--   - encoding: m(q, z) and next(q, z) undefined for q ∈ F → read off the instruction stored at q (CounterMachine.instr is total); reason: a realizer never outputs a halting state (conjunct G ⋀ q₁ ≠ q and PathAgr), so these values are never used
--   - encoding: arithmetic constraints on output components used as atomic propositions → finite disjunctions of (conjunctions of) output atoms; reason: the paper's own reading of these abbreviations (p. 21–22)
--   - encoding: zero ∈ {⊤, ⊥}, pos ∈ Z₃, carry ∈ {0, …, 8} → Bool (true = ⊤), Fin 3, Fin 9; reason: same sets
--   - encoding: singleton input sets → X_1 = X_2 = Unit; reason: the same instances
--   - encoding: f_p : Views_p → Y_p → f_p is a total function on the inductive type of view terms; reason: values on terms that are not process-p views never enter an execution, so the realizable specifications are the same
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), p. 28 (PDF 29), Theorem 6.12; formula Eq. (31), p. 24 (PDF 25)

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL
import Definitions.Def_DistLTLSynth_Char_CounterMachine
import Definitions.Def_DistLTLSynth_Char_CounterFormula

namespace DistLTLSynth.Char

/-- Theorem 6.12: a 1-counter machine `M_counter` does not halt iff `ϕ(M_counter)` (Eq. (31))
is realizable (under the full adversary `Γ^ω`, singleton inputs). -/
theorem theorem_6_12 {Q : Type} [Fintype Q] [DecidableEq Q] (M : CounterMachine Q 1) :
    ¬ M.Halts ↔ Realizable Set.univ (counterFormula M) := by sorry

end DistLTLSynth.Char
