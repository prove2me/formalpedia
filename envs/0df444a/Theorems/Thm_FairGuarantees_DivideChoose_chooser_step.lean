-- Prove2me | Theorems.Thm_FairGuarantees_DivideChoose_chooser_step
-- name    : FairGuarantees.DivideChoose.chooser_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:33.634083+00:00
-- url     : https://prove2.me/theorems/a18006b1-7d2a-4682-aa38-52d6db5e6e6a
-- title:
--   Proof of Theorem 1 i), p. 15 — in any n-partition whose old parts are worth < minMax(u; n), a fresh part is worth ≥ minMax(u; n)
-- statement:
--   Let $u\in\mathcal D(\Omega)$, $n\ge1$, and let $(Q_j)_{j=1}^n\in\mathcal P_n(\Omega)$. Let $\mathrm{Old}\subseteq\{1,\dots,n\}$ be a set of indices with $u(Q_j)<\mathrm{minMax}(u;n)$ for all $j\in\mathrm{Old}$. Then some $j\notin\mathrm{Old}$ has
--   $$u(Q_j)\ge\mathrm{minMax}(u;n).$$
--
--   In the proof of Theorem 1 i), the old parts are the shares assigned before the current step and the other parts are the freshly cut shares: an agent using the minMax strategy can always find a share to accept.
--
--   **Formalization Note** Run-free form of the paper's argument; the run-level statement is part 2 of the goal theorem.
-- source:
--   Bogomolnaia & Moulin, Guarantees in Fair Division, arXiv:1911.10009v3, p. 15, §4, proof of Theorem 1, Statement i), first paragraph

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting

namespace FairGuarantees.DivideChoose

/-- Proof of Theorem 1 i), p. 15, first paragraph: if `Q` is an `n`-partition of `Ω` whose
parts indexed by `Old` are all worth strictly less than `minMax(u; n)`, then some part not in
`Old` is worth at least `minMax(u; n)`. -/
theorem chooser_step {d n : ℕ} (hn : 0 < n) {Ω : Set (E d)} (hΩ : IsManna Ω)
    {u : Set (E d) → ℝ} (hu : IsUtility Ω u) {Q : Fin n → Set (E d)} (hQ : IsPartition Ω Ω n Q)
    (Old : Finset (Fin n)) (hOld : ∀ j ∈ Old, u (Q j) < minMax Ω u n) :
    ∃ j ∉ Old, minMax Ω u n ≤ u (Q j) := by sorry

end FairGuarantees.DivideChoose
