-- Prove2me | Theorems.Thm_FixedMachinePrec_theorem_5_9
-- name    : FixedMachinePrec.theorem_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:07:40.777298+00:00
-- url     : https://prove2.me/theorems/75094b6d-310b-47d1-93af-183c5875f5b8
-- title:
--   Theorem 5.9 — completeness from a described hierarchy
-- statement:
--   Let $m\ge1$, let $\prec$ be a strict partial order on $J$, let $\mathcal F\subseteq2^J$ be a finite family containing $\emptyset$ and $J$, and let $\mathcal F_{\mathrm{cut}}\subseteq2^J$ be a finite cut family. Then Algorithm 4 accepts, $a(W)=1$, every set $W$ that is the root of a hierarchy described by $(\mathcal F,\mathcal F_{\mathrm{cut}})$; in particular every node set of a described hierarchy, and the root $J$ whenever $J$ has a described hierarchy.
--
--   Together with Theorem 5.8 this makes the deadline test complete.
--
--   Differences from the source:
--   - generalization: the scope m ≥ 3 of the explicit procedures (p.1) → every m ≥ 1; reason: the theorem and its proof place no restriction on m ≥ 1; m ≥ 3 is a case
--   - generalization: every node set of a described hierarchy with root J → every root W of a described hierarchy (the subtree at a node); reason: the subtree below a node of a described hierarchy is a described hierarchy with that root
--   - encoding: jobs 1, …, n and padded jobs 1, …, N → Fin n and Fin N (0-based labels); reason: Lean convention; the shift changes no instance
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), Theorem 5.9, p.18

import Mathlib
import Definitions.Def_FixedMachinePrec_EvaluateFamily
import Definitions.Def_FixedMachinePrec_Hierarchy

namespace FixedMachinePrec

/-- **Theorem 5.9 (Completeness from a described hierarchy).** Jansen, *Precedence Constraint
Scheduling on a Fixed Number of Machines* (manuscript, sha256 08cdf3e1…), Theorem 5.9, p.18: "Let
F ⊆ 2^J be a finite family containing ∅ and J, and let F_cut ⊆ 2^J be a finite cut family. If the
full instance on J has a hierarchy described by (F, F_cut) in the sense of Definition 5.7, then
Algorithm 4 accepts every node set of the hierarchy. In particular, it accepts the root J."

For every finite `F ∋ ∅, J` and every finite `F_cut`: every set `W` that is the root of a
hierarchy described by `(F, F_cut)` (in particular every node of a described hierarchy with root
`J`, and `J` itself) is accepted by Algorithm 4, `a(W) = 1`.

**Formalization Note** `J = Fin N` with a strict partial order. The subtree below a node of a
described hierarchy is a described hierarchy with that node as root, so "every node set" is
"every root of a described hierarchy"; the root clause is the case `W = J`. -/
theorem theorem_5_9 {N : ℕ} (m : ℕ) (hm : 1 ≤ m) (prec : Fin N → Fin N → Prop) [DecidableRel prec]
    (hprec : IsStrictOrder' prec) (F Fcut : Finset (Finset (Fin N))) (hF0 : ∅ ∈ F)
    (hFJ : Finset.univ ∈ F) :
    (∀ W : Finset (Fin N), Described prec m F Fcut W →
      (evaluateFamily prec m F Fcut W).isSome = true) ∧
    (Described prec m F Fcut Finset.univ →
      (evaluateFamily prec m F Fcut Finset.univ).isSome = true) := by sorry

end FixedMachinePrec
