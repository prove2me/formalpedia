-- Prove2me | Theorems.Thm_FixedMachinePrec_corollary_7_5
-- name    : FixedMachinePrec.corollary_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:07:24.281901+00:00
-- url     : https://prove2.me/theorems/1c2d5ade-af3b-4eef-9a91-f59a3cc49bbb
-- title:
--   Corollary 7.5 — an actual separator exists
-- statement:
--   Let $m\ge3$, let $\prec$ be a strict partial order on $J$, and let $U\subseteq J$ be nonempty.
--
--   1. If $(Z_1,\dots,Z_q)$ is a full schedule of $U$ normalized for a priority order $u_1\lhd_U\dots\lhd_U u_s$, then every priority prefix $S_k=\{u_1,\dots,u_k\}$, $0\le k\le|U|$, is separated by some actual slot $Z_r$, $1\le r\le q$.
--   2. If $U$ has a feasible full schedule, then every ideal $I$ of $U$ is separated by an actual slot of some feasible full schedule of $U$.
--
--   Separators are what the structural construction marks; this corollary guarantees one is always available.
--
--   Differences from the source:
--   - generalization: a nonempty normalized full schedule (of the contiguous interval domain of §7.2) → a normalized full schedule of an arbitrary nonempty domain U ⊆ J; reason: normalization compares only schedules of U (p.30), and the proof of the second assertion applies the first to an arbitrary feasible full-slot domain; the interval domain is one case
--   - encoding: jobs 1, …, n and padded jobs 1, …, N → Fin n and Fin N (0-based labels); reason: Lean convention; the shift changes no instance
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), Corollary 7.5, p.37

import Mathlib
import Definitions.Def_FixedMachinePrec_Separator

namespace FixedMachinePrec

/-- **Corollary 7.5 (An actual separator).** Jansen, *Precedence Constraint Scheduling on a Fixed
Number of Machines* (manuscript, sha256 08cdf3e1…), Corollary 7.5, p.37: "Every priority prefix in
a nonempty normalized full schedule has an actual separator. Every ideal of a feasible nonempty
full-slot domain has an actual separator in some feasible full schedule of that domain."

1. If `Zs` is a full schedule of a nonempty domain `U` that is normalized for a priority order
   `pri` on `U`, then every priority prefix `S_k = {u_1, …, u_k}` (`0 ≤ k ≤ |U|`) is separated by
   some actual slot `Z_r`, `1 ≤ r ≤ q`.
2. If a nonempty domain `U` has a feasible full schedule, then every ideal `I` of `U` is separated
   by an actual slot of some feasible full schedule of `U`.

**Formalization Note** The domain `U` is an arbitrary subset of `J = Fin N`, as in the proof of the
second assertion, which applies the first to an arbitrary feasible full-slot domain. Cones are
computed on all of `J`. -/
theorem corollary_7_5 {N : ℕ} (m : ℕ) (hm : 3 ≤ m) (prec : Fin N → Fin N → Prop)
    [DecidableRel prec] (hprec : IsStrictOrder' prec) (U : Finset (Fin N)) (hU : U.Nonempty) :
    (∀ (pri : List (Fin N)) (Zs : List (Finset (Fin N))), IsPriorityList prec U pri →
      IsNormalized prec m U pri Zs →
      ∀ k ≤ U.card, ∃ r : ℕ, Separates prec Zs (priorityPrefix pri k) r) ∧
    ((∃ Zs : List (Finset (Fin N)), IsFullSchedule prec m U Zs) →
      ∀ I : Finset (Fin N), IsIdealIn prec U I →
        ∃ Zs : List (Finset (Fin N)), IsFullSchedule prec m U Zs ∧ ∃ r : ℕ, Separates prec Zs I r) := by sorry

end FixedMachinePrec
