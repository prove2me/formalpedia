-- Prove2me | Theorems.Thm_FixedMachinePrec_lemma_7_1
-- name    : FixedMachinePrec.lemma_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:06:58.47622+00:00
-- url     : https://prove2.me/theorems/2d70b416-a46a-42bb-a334-71902898ef4b
-- title:
--   Lemma 7.1 — replacement and prefix minimality
-- statement:
--   Let $m\ge3$, let $\prec$ be a strict partial order on $J$, and let $\sigma=(S_1,\dots,S_T)$ be a feasible full schedule of $J$. For boundary positions $0\le a<b\le T+1$ let $U=\bigcup_{a<t<b}S_t$ and let $(S_{a+1},\dots,S_{b-1})$ be its current local schedule.
--
--   1. **Replacement.** For every feasible full schedule $\pi$ of $U$, the schedule $(S_1,\dots,S_a)\,\pi\,(S_b,\dots,S_T)$ is a feasible full schedule of $J$.
--   2. **Prefix minimality.** Let $\lhd_U$ be a priority order on $U$ for which the local schedule is normalized, and let $1\le r\le b-a-1$. Let $\rho$ be any feasible full schedule of $U$ agreeing with the local schedule in its first $r$ slots. If $y$ lies in slot $r$ of $\rho$, $x\in U$ lies in a later slot of $\rho$, and $x\lhd_U y$, then exchanging the slots of $x$ and $y$ in $\rho$ does not give a feasible full schedule of $U$.
--
--   **Formalization Note** One fixed frame; stating the lemma for every strict partial order covers the reversed frame. The exchange is tested on $U$'s local schedule.
--
--   Differences from the source:
--   - encoding: a contiguous interval of the witness → the jobs of slots a+1, …, b−1 for positions 0 ≤ a < b ≤ T+1; reason: the paper's temporal interval (a, b), §7.1
--   - reading: no feasible exchange (in the complete schedule) → the exchanged local schedule of U is not a feasible full schedule of U; reason: by clause 1 and restriction, an exchange inside U is feasible for the complete schedule iff it is feasible for U
--   - encoding: jobs 1, …, n and padded jobs 1, …, N → Fin n and Fin N (0-based labels); reason: Lean convention; the shift changes no instance
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), Lemma 7.1, p.32

import Mathlib
import Definitions.Def_FixedMachinePrec_Separator

namespace FixedMachinePrec

/-- **Lemma 7.1 (Replacement and prefix minimality).** Jansen, *Precedence Constraint Scheduling on
a Fixed Number of Machines* (manuscript, sha256 08cdf3e1…), Lemma 7.1, p.32: "Let U be the jobs in
a contiguous interval of a complete feasible full witness schedule in a fixed frame. Every feasible
full schedule of U can replace its current schedule within the same slots, with all jobs outside U
fixed. Fix also a priority order on U, and suppose its current local schedule is normalized for
that priority. Let r be one of its slots. After any feasible reordering of the jobs in slots of U
strictly after r, keeping r and all earlier slots unchanged, no feasible exchange can replace a job
y ∈ r by a later job x ∈ U with x ◁_U y."

Let `σ = (S_1, …, S_T)` be a feasible full schedule of `J = Fin N`, and `0 ≤ a < b ≤ T + 1`
boundary positions; `U = (a, b)` is the set of jobs in slots `a+1, …, b−1` and
`Zs = (S_{a+1}, …, S_{b−1})` its current local schedule.
1. For every feasible full schedule `π` of `U`, `(S_1, …, S_a) ++ π ++ (S_b, …, S_T)` is a feasible
   full schedule of `J`.
2. Let `pri` be a priority order on `U` for which `Zs` is normalized, and `1 ≤ r ≤ |Zs|`. Let `ρ`
   be a feasible full schedule of `U` that agrees with `Zs` in its first `r` slots. If `y` is in
   slot `r` of `ρ`, `x ∈ U` is in a later slot of `ρ`, and `x ◁_U y`, then exchanging the slots of
   `x` and `y` in `ρ` does not give a feasible full schedule of `U`.

**Formalization Note** One fixed frame: stating the lemma for every strict partial order covers the
reversed frame. An exchange is feasible for the complete schedule iff it is feasible for `U`'s
local schedule, by clause 1 and restriction; clause 2 uses the local form. -/
theorem lemma_7_1 {N : ℕ} (m : ℕ) (hm : 3 ≤ m) (prec : Fin N → Fin N → Prop) [DecidableRel prec]
    (hprec : IsStrictOrder' prec) (σ : List (Finset (Fin N)))
    (hσ : IsFullSchedule prec m Finset.univ σ) (a b : ℕ) (hab : a < b) (hb : b ≤ σ.length + 1) :
    let Zs := (σ.drop a).take (b - 1 - a)
    let U := slotsBetween σ a b
    (∀ π : List (Finset (Fin N)), IsFullSchedule prec m U π →
      IsFullSchedule prec m Finset.univ (σ.take a ++ π ++ σ.drop (b - 1))) ∧
    (∀ pri : List (Fin N), IsPriorityList prec U pri → IsNormalized prec m U pri Zs →
      ∀ r : ℕ, 1 ≤ r → r ≤ Zs.length →
      ∀ ρ : List (Finset (Fin N)), IsFullSchedule prec m U ρ → ρ.take r = Zs.take r →
      ∀ x y : Fin N, y ∈ ρ.getD (r - 1) ∅ → x ∈ U → r < localTime ρ x →
        pri.idxOf x < pri.idxOf y → ¬ IsFullSchedule prec m U (swapJobs ρ x y)) := by sorry

end FixedMachinePrec
