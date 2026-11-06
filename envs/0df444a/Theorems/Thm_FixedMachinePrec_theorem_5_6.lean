-- Prove2me | Theorems.Thm_FixedMachinePrec_theorem_5_6
-- name    : FixedMachinePrec.theorem_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:06:59.854615+00:00
-- url     : https://prove2.me/theorems/8ac6e818-940d-473d-98ab-e174a7560628
-- title:
--   Theorem 5.6 — soundness of Algorithm 4 for every family
-- statement:
--   Let $m\ge1$ and let $\prec$ be a strict partial order on $J$. Let $\mathcal F\subseteq2^J$ be any finite family containing $\emptyset$ and $J$, and $\mathcal F_{\mathrm{cut}}\subseteq2^J$ any finite cut family. If Algorithm 4 assigns value one to a row $X$, then the schedule $\sigma(X)$ it stores is a feasible full schedule of $X$.
--
--   Every acceptance is therefore certified by an explicit schedule, whatever families are used.
--
--   Differences from the source:
--   - generalization: the scope m ≥ 3 of the explicit procedures (p.1) → every m ≥ 1; reason: the theorem and its proof place no restriction on m ≥ 1; m ≥ 3 is a case
--   - encoding: jobs 1, …, n and padded jobs 1, …, N → Fin n and Fin N (0-based labels); reason: Lean convention; the shift changes no instance
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), Theorem 5.6, p.14

import Mathlib
import Definitions.Def_FixedMachinePrec_EvaluateFamily

namespace FixedMachinePrec

/-- **Theorem 5.6 (Soundness for every explicit family).** Jansen, *Precedence Constraint Scheduling
on a Fixed Number of Machines* (manuscript, sha256 08cdf3e1…), Theorem 5.6, p.14: "Every row
assigned value one by Algorithm 4 stores a feasible full schedule of its set. This holds for every
family F containing ∅ and J, and every finite cut family F_cut ⊆ 2^J."

For every finite family `F ∋ ∅, J` and every finite cut family `F_cut`, if the table returned by
Algorithm 4 stores `σ(X) = S` (that is, `a(X) = 1`), then `S` is a feasible full schedule of `X`.

**Formalization Note** `J = Fin N` with a strict partial order `prec`; families are finite sets of
subsets of `J`. -/
theorem theorem_5_6 {N : ℕ} (m : ℕ) (hm : 1 ≤ m) (prec : Fin N → Fin N → Prop) [DecidableRel prec]
    (hprec : IsStrictOrder' prec) (F Fcut : Finset (Finset (Fin N))) (hF0 : ∅ ∈ F)
    (hFJ : Finset.univ ∈ F) (X : Finset (Fin N)) (S : List (Finset (Fin N)))
    (hX : evaluateFamily prec m F Fcut X = some S) :
    IsFullSchedule prec m X S := by sorry

end FixedMachinePrec
