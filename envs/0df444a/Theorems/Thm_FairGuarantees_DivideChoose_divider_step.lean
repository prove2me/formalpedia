-- Prove2me | Theorems.Thm_FairGuarantees_DivideChoose_divider_step
-- name    : FairGuarantees.DivideChoose.divider_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:35.238047+00:00
-- url     : https://prove2.me/theorems/66a7ad3c-0419-4d63-b22a-b76332000e37
-- title:
--   Proof of Theorem 1 i), p. 15 — an equipartition completing old parts worth < minMax(u; n) is worth ≥ minMax(u; n)
-- statement:
--   Let $u\in\mathcal D(\Omega)$, $n\ge1$, and let $(Q_j)_{j=1}^n\in\mathcal P_n(\Omega)$ consist of old parts $Q_j$, $j\in\mathrm{Old}$, each with $u(Q_j)<\mathrm{minMax}(u;n)$, and at least one fresh part $Q_j$, $j\notin\mathrm{Old}$, with all fresh parts of the same utility (an equipartition $\Pi^e$ of the remaining manna). Then
--   $$u(\Pi^e)=u(Q_j)\ge\mathrm{minMax}(u;n)\qquad\text{for every } j\notin\mathrm{Old}.$$
--
--   In the proof of Theorem 1 i) this shows that the Divider's equipartition gives the Divider at least the initial minMax level.
--
--   **Formalization Note** The equipartition and the old shares are given as one $n$-partition `Q` of $\Omega$; the parts outside `Old` are the nonempty equipartition, which has equal values.
-- source:
--   Bogomolnaia & Moulin, Guarantees in Fair Division, arXiv:1911.10009v3, p. 15, §4, proof of Theorem 1, Statement i), second paragraph

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting

namespace FairGuarantees.DivideChoose

/-- Proof of Theorem 1 i), p. 15, second paragraph: if `Q` is an `n`-partition of `Ω` made of
old parts (indexed by `Old`), each worth strictly less than `minMax(u; n)`, and of the parts of
an equipartition (the parts outside `Old`, all of equal utility), then the common utility of
the equipartition is at least `minMax(u; n)`. -/
theorem divider_step {d n : ℕ} (hn : 0 < n) {Ω : Set (E d)} (hΩ : IsManna Ω)
    {u : Set (E d) → ℝ} (hu : IsUtility Ω u) {Q : Fin n → Set (E d)} (hQ : IsPartition Ω Ω n Q)
    (Old : Finset (Fin n)) (hfresh : ∃ j, j ∉ Old)
    (hOld : ∀ j ∈ Old, u (Q j) < minMax Ω u n)
    (hequi : ∀ j ∉ Old, ∀ k ∉ Old, u (Q j) = u (Q k)) :
    ∀ j ∉ Old, minMax Ω u n ≤ u (Q j) := by sorry

end FairGuarantees.DivideChoose
