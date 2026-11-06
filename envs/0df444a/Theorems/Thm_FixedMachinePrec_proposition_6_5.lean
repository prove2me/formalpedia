-- Prove2me | Theorems.Thm_FixedMachinePrec_proposition_6_5
-- name    : FixedMachinePrec.proposition_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:09:31.09874+00:00
-- url     : https://prove2.me/theorems/a262d4ab-bd1d-4c71-8c9a-27ee9368b4cd
-- title:
--   Proposition 6.5 — multitape bound $O(L)+m^{O(m^2)}n^{12m^2+26m+2}\log^3n$
-- statement:
--   There are multitape Turing machines $M_{\mathrm{opt}}$, $M_{\mathrm{dl}}$ and one constant $c$ such that for every $m\ge3$ and every acyclic instance $G$ with distinct arcs:
--
--   1. $M_{\mathrm{opt}}$ outputs exactly the optimum schedule constructed by Algorithm 7 within
--   $$c\,L+m^{c m^2}n^{12m^2+26m+2}\lfloor\log_2n\rfloor^3$$
--   steps;
--   2. for every deadline $T$, $M_{\mathrm{dl}}$ outputs exactly the answer of Algorithm 6 within
--   $$c\,L_T+m^{c m^2}n^{12m^2+26m+2}\lfloor\log_2n\rfloor^2$$
--   steps.
--
--   The algorithms of the paper thus run in polynomial time for every fixed $m$ also on a deterministic Turing machine with a fixed number of tapes.
--
--   **Formalization Note** Turing machines are Mathlib's multi-stack `TM2` machines with finitely many stacks.
--
--   Differences from the source:
--   - encoding: a deterministic Turing machine with a fixed number of tapes → Mathlib's Turing.TM2ComputableAux Bool Bool (finitely many stacks); reason: a tape is two stacks and a stack is a tape, with constant overhead per step
--   - reading: the algorithms of this paper can be implemented → the machines output the encodings of the values of the Lean functions optimum and deadline; reason: implementation means computing the same outputs
--   - encoding: O(L) + m^{O(m²)} f and log n → c·L + m^{c·m²}·f with one c, and ⌊log₂ n⌋; reason: uniform constant; equal up to a factor 2 for n ≥ 2
--   - encoding: log n in the bounds, for n ≤ 1 → Nat.log2 n = 0, so the bound is c·L (c·L_T with a deadline); reason: as printed the log factor vanishes there; instances with n ≤ 1 take O(L + 1), proof of Theorem 6.4, p.24
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), Proposition 6.5, p.25

import Mathlib
import Definitions.Def_FixedMachinePrec_Deadline
import Definitions.Def_FixedMachinePrec_Encoding
import Definitions.Def_HMBinPacking_OutputsWithin

namespace FixedMachinePrec

/-- **Proposition 6.5 (A conservative multitape bound).** Jansen, *Precedence Constraint Scheduling
on a Fixed Number of Machines* (manuscript, sha256 08cdf3e1…), Proposition 6.5, p.25: "The
algorithms of this paper can be implemented on a deterministic Turing machine with a fixed number
of tapes. Optimization and construction of an optimum schedule take
O(L) + m^{O(m²)} n^{12m²+26m+2} log³ n steps. A single deadline test uses log² n in place of
log³ n."

There are Turing machines `Mopt`, `Mdl` and one constant `c` such that for every `m ≥ 3` and every
acyclic instance with distinct arcs:
1. `Mopt` outputs exactly the encoding of the schedule returned by Algorithm 7 within
   `c·L + m^{c·m²}·n^{12m²+26m+2}·⌊log₂ n⌋³` steps;
2. for every deadline `T`, `Mdl` outputs exactly the encoding of the answer of Algorithm 6 within
   `c·L_T + m^{c·m²}·n^{12m²+26m+2}·⌊log₂ n⌋²` steps.

**Formalization Note** "Implemented" is read as: the machine outputs what the Lean functions
`optimum` and `deadline` (Algorithms 7 and 6) return. Turing machines are Mathlib's multi-stack
`TM2` machines with finitely many stacks (the published `HMBinPacking.OutputsWithin`, Mathlib's `Turing.TM2OutputsInTime`). The statement covers every `n`. -/
theorem proposition_6_5 :
    ∃ (Mopt Mdl : Turing.TM2ComputableAux Bool Bool) (c : ℕ),
      ∀ m : ℕ, 3 ≤ m → ∀ G : Instance, G.Acyclic → G.arcs.Nodup →
        (∃ t : ℕ, HMBinPacking.OutputsWithin Mopt (encInput m G) (encSchedule (optimum G m).2) t ∧
          t ≤ c * (encInput m G).length +
            m ^ (c * m ^ 2) * G.n ^ (12 * m ^ 2 + 26 * m + 2) * Nat.log2 G.n ^ 3) ∧
        (∀ T : ℕ, ∃ t : ℕ,
          HMBinPacking.OutputsWithin Mdl (encDeadlineInput m G T) (encDeadlineResult (deadline G m T)) t ∧
          t ≤ c * (encDeadlineInput m G T).length +
            m ^ (c * m ^ 2) * G.n ^ (12 * m ^ 2 + 26 * m + 2) * Nat.log2 G.n ^ 2) := by sorry

end FixedMachinePrec
