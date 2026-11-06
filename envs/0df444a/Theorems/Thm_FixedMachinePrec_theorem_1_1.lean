-- Prove2me | Theorems.Thm_FixedMachinePrec_theorem_1_1
-- name    : FixedMachinePrec.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:07:59.69452+00:00
-- url     : https://prove2.me/theorems/fdbfac1e-f1bb-4ff3-a5c2-14e49186064b
-- title:
--   Theorem 1.1 — an optimum schedule for $Pm\mid prec,p_j=1\mid C_{\max}$ in $O(L)+m^{O(m^2)}n^{6m^2+13m+1}\log n$ RAM operations, for every $m\ge3$
-- statement:
--   There are RAM programs $P_{\mathrm{opt}},P_{\mathrm{dl}}$, multitape Turing machines $M_{\mathrm{opt}},M_{\mathrm{dl}}$ and one constant $c$, all fixed before $m$, such that for every integer $m\ge3$ and every acyclic precedence graph $G$ with distinct arcs on $n\ge2$ unit jobs (input length $L$, or $L_T$ with a deadline $T$):
--
--   1. at every word size $W\ge c\,m^2(\lfloor\log_2(mn)\rfloor+1)$, $P_{\mathrm{opt}}$ outputs an optimum schedule within
--   $$c\,L+m^{cm^2}n^{6m^2+13m+1}\log n\qquad\text{and within}\qquad c\,L+m^{cm^2}n^{11m^2}$$
--   elementary RAM operations;
--   2. at every such word size and for every nonnegative integer deadline $T$, $P_{\mathrm{dl}}$ decides deadline feasibility (returning a schedule of makespan at most $T$ on YES) within $c\,L_T+m^{cm^2}n^{6m^2+13m+1}$ operations — no logarithmic factor;
--   3. $M_{\mathrm{opt}}$ outputs an optimum schedule within $c\,L+m^{cm^2}n^{12m^2+26m+2}\log^3n$ steps;
--   4. for every $T$, $M_{\mathrm{dl}}$ decides deadline feasibility within $c\,L_T+m^{cm^2}n^{12m^2+26m+2}\log^2n$ steps.
--
--   Here an optimum schedule has makespan at most that of every feasible nonpreemptive schedule with real start times, and $\log$ is $\lfloor\log_2\rfloor$. The running time is polynomial for every fixed $m$, and the algorithm is uniform in $m$.
--
--   **Formalization Note** The schedule is output as an integral slot and machine assignment; its real-time reading is checked.
--
--   Differences from the source:
--   - encoding: O(L) + m^{O(m²)} f, “the algorithm is uniform” → c·L + m^{c·m²}·f with one constant c and one program per task, chosen before m; reason: this is the uniform reading the theorem states
--   - reading: the RAM model of Section 6 (words of O(m² log(N + 2)) bits, N ≤ mn) → RAMInstr with input/output tapes, correct at every word size W ≥ c·m²·(⌊log₂(mn)⌋ + 1); reason: N ≤ mn, and N ≥ max(m, n) when padding is used, so the thresholds agree up to a constant
--   - encoding: a deterministic Turing machine with a fixed number of tapes → Mathlib's Turing.TM2ComputableAux Bool Bool; reason: tapes and stacks simulate each other with constant overhead per step
--   - encoding: binary input of length L with listed vertices and distinct arcs → encInput: self-delimiting binary codes of m, n, the labels, the arc count and the arcs; acyclicity and distinct arcs as hypotheses; reason: the length is the binary input length up to a constant factor
--   - generalization: decide deadline feasibility → output the verdict and, on YES, a schedule meeting T; reason: the verdict bit is the decision; Theorem 6.4 includes the reconstruction
--   - encoding: log n → ⌊log₂ n⌋ (Nat.log2); reason: equal up to a factor 2 for n ≥ 2
--   - encoding: jobs 1, …, n and padded jobs 1, …, N → Fin n and Fin N (0-based labels); reason: Lean convention; the shift changes no instance
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), Theorem 1.1, p.1

import Mathlib
import Definitions.Def_FixedMachinePrec_Encoding
import Definitions.Def_FixedMachinePrec_RAM
import Definitions.Def_HMBinPacking_OutputsWithin

namespace FixedMachinePrec

/-- **Theorem 1.1 (An exact algorithm for fixed machine capacity).** Jansen, *Precedence Constraint
Scheduling on a Fixed Number of Machines* (manuscript, sha256 08cdf3e1…), Theorem 1.1, p.1: "For
every integer m ≥ 3 and n ≥ 2, there are algorithms to decide deadline feasibility and construct an
optimum schedule using O(L) + m^{O(m²)} n^{6m²+13m+1} log n (1) elementary RAM operations in the
model specified in Section 6. A single deadline test needs no logarithmic search factor. In
particular, the simpler uniform bound O(L) + m^{O(m²)} n^{11m²} holds for optimization as well. On
a deterministic Turing machine with a fixed number of tapes, optimization and construction of an
optimum schedule take O(L) + m^{O(m²)} n^{12m²+26m+2} log³ n steps. A single deadline test uses
log² n instead of log³ n in this multitape bound … The algorithm is uniform: all constants,
families, and loops are specified as functions of its input."

There are RAM programs `Popt`, `Pdl`, Turing machines `Mopt`, `Mdl` and one constant `c`, chosen
before `m`, such that for every `m ≥ 3` and every acyclic instance with distinct arcs and `n ≥ 2`
jobs (with `L` the input length and `lg = ⌊log₂ n⌋`):
1. at every word size `W ≥ c·m²·(⌊log₂(mn)⌋ + 1)`, `Popt` outputs an optimum schedule within
   `c·L + m^{c·m²}·n^{6m²+13m+1}·lg` and within `c·L + m^{c·m²}·n^{11m²}` operations;
2. at every such word size and for every deadline `T`, `Pdl` outputs the correct verdict, with a
   schedule meeting `T` on YES, within `c·L_T + m^{c·m²}·n^{6m²+13m+1}` operations;
3. `Mopt` outputs an optimum schedule within `c·L + m^{c·m²}·n^{12m²+26m+2}·lg³` steps;
4. for every `T`, `Mdl` outputs the correct deadline answer within
   `c·L_T + m^{c·m²}·n^{12m²+26m+2}·lg²` steps.

**Formalization Note** `O(L) + m^{O(m²)} f` is `c·L + m^{c·m²}·f` for one constant `c`. "The model
specified in Section 6" has words of `O(m² log(N + 2))` bits for the padded size `N ≤ mn` (p.20);
this is read as: correct at every word size from `c·m²(⌊log₂(mn)⌋ + 1)` on.
"Optimum" is against every feasible schedule with real start times. The deadline test also returns
a schedule on YES (Theorem 6.4: "deadline feasibility and reconstruction of a schedule"). -/
theorem theorem_1_1 :
    ∃ (Popt Pdl : List RAMInstr) (Mopt Mdl : Turing.TM2ComputableAux Bool Bool) (c : ℕ),
      ∀ m : ℕ, 3 ≤ m → ∀ G : Instance, G.Acyclic → G.arcs.Nodup → 2 ≤ G.n →
        (∀ W : ℕ, c * m ^ 2 * (Nat.log2 (m * G.n) + 1) ≤ W →
          ∃ (out : List Bool) (t : ℕ), RAMOutputs W Popt (encInput m G) out t ∧
            IsOptimumOutput m G out ∧
            t ≤ c * (encInput m G).length +
              m ^ (c * m ^ 2) * G.n ^ (6 * m ^ 2 + 13 * m + 1) * Nat.log2 G.n ∧
            t ≤ c * (encInput m G).length + m ^ (c * m ^ 2) * G.n ^ (11 * m ^ 2)) ∧
        (∀ T W : ℕ, c * m ^ 2 * (Nat.log2 (m * G.n) + 1) ≤ W →
          ∃ (out : List Bool) (t : ℕ), RAMOutputs W Pdl (encDeadlineInput m G T) out t ∧
            IsDeadlineOutput m G T out ∧
            t ≤ c * (encDeadlineInput m G T).length +
              m ^ (c * m ^ 2) * G.n ^ (6 * m ^ 2 + 13 * m + 1)) ∧
        (∃ (out : List Bool) (t : ℕ), HMBinPacking.OutputsWithin Mopt (encInput m G) out t ∧
            IsOptimumOutput m G out ∧
            t ≤ c * (encInput m G).length +
              m ^ (c * m ^ 2) * G.n ^ (12 * m ^ 2 + 26 * m + 2) * Nat.log2 G.n ^ 3) ∧
        (∀ T : ℕ, ∃ (out : List Bool) (t : ℕ), HMBinPacking.OutputsWithin Mdl (encDeadlineInput m G T) out t ∧
            IsDeadlineOutput m G T out ∧
            t ≤ c * (encDeadlineInput m G T).length +
              m ^ (c * m ^ 2) * G.n ^ (12 * m ^ 2 + 26 * m + 2) * Nat.log2 G.n ^ 2) := by sorry

end FixedMachinePrec
