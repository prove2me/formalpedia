-- Prove2me | Theorems.Thm_FairGuarantees_BidChoose_proposition_1_ii
-- name    : FairGuarantees.BidChoose.proposition_1_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:53.208345+00:00
-- url     : https://prove2.me/theorems/62f3cb37-ec36-45fc-a0cf-1963e1a65de8
-- title:
--   Proposition 1 ii), p. 11, eq. (3) — for u ∈ M⁺(Ω), minMax and Maxmin are the extreme equipartition utilities
-- statement:
--   Let $n\ge1$, $\Omega\subseteq\mathbb R^d$ ($d\ge1$) a manna and $u\in\mathcal D(\Omega)\cap\mathcal M^+(\Omega)$. Then
--   $$
--   \mathit{minMax}(u;n)=\inf_{\Pi^e\in\mathcal{EP}_n(\Omega;u)}u(\Pi^e),\qquad
--   \mathit{Maxmin}(u;n)=\sup_{\Pi^e\in\mathcal{EP}_n(\Omega;u)}u(\Pi^e).
--   $$
--
--   For monotone utilities, the two benchmarks are thus attained (up to the infimum and supremum) on equipartitions, which is how any equipartition value is compared with them.
--
--   **Formalization Note.** The paper's min/max are read as inf/sup (p. 9). $u(\Pi^e)$ is the utility of the first share of $\Pi^e$, which equals that of every share. Only the case $\mathcal M^+(\Omega)$ is stated; the paper's $\mathcal M^-(\Omega)$ case is symmetric and not used by this mission. The equalities include the nonemptiness of $\mathcal{EP}_n(\Omega;u)$ in this domain, since the infimum and supremum of an empty set are junk values in Lean.
-- source:
--   Bogomolnaia & Moulin, Guarantees in Fair Division, arXiv:1911.10009v3, p. 11, Proposition 1 ii), eq. (3); proof pp. 11–12

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting
import Definitions.Def_FairGuarantees_BidChoose_Guarantees

open MeasureTheory

namespace FairGuarantees.BidChoose

/-- Proposition 1 ii), p. 11, display (3), for `u ∈ M⁺(Ω)`: `minMax(u; n)` is the infimum and
`Maxmin(u; n)` the supremum of the common utility `u(Πᵉ)` over the `n`-equipartitions `Πᵉ`
of `Ω`. -/
theorem proposition_1_ii {d n : ℕ} [NeZero n] (hd : 0 < d) {Ω : Set (FairGuarantees.DivideChoose.E d)} (hΩ : FairGuarantees.DivideChoose.IsManna Ω)
    {u : Set (FairGuarantees.DivideChoose.E d) → ℝ} (hu : FairGuarantees.DivideChoose.IsUtility Ω u) (hinc : FairGuarantees.DivideChoose.IsIncreasing Ω u) :
    FairGuarantees.DivideChoose.minMax Ω u n = sInf {x | ∃ P : Fin n → Set (FairGuarantees.DivideChoose.E d), FairGuarantees.DivideChoose.IsEquipartition Ω u Ω n P ∧
        x = u (P ⟨0, Nat.pos_of_neZero n⟩)} ∧
    FairGuarantees.DivideChoose.Maxmin Ω u n = sSup {x | ∃ P : Fin n → Set (FairGuarantees.DivideChoose.E d), FairGuarantees.DivideChoose.IsEquipartition Ω u Ω n P ∧
        x = u (P ⟨0, Nat.pos_of_neZero n⟩)} := by sorry

end FairGuarantees.BidChoose
