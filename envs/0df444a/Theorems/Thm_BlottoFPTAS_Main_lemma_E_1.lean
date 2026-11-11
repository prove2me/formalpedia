-- Prove2me | Theorems.Thm_BlottoFPTAS_Main_lemma_E_1
-- name    : BlottoFPTAS.Main.lemma_E_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:43:10.626722+00:00
-- url     : https://prove2.me/theorems/065a609c-9b89-45db-99f8-73eda1dfef58
-- title:
--   Lemma E.1 — an anchor table in P(γ), γ > β, keeps every row feasible and raises the opponent's supremum by at most m/S
-- statement:
--   Fix $m\ge2$ battlefields with positive values $w$ summing to one, $e=2^{-a}$, a label table in which every label has probability $1/K$ on every battlefield, an anchor table $u$ satisfying the static constraints (in particular every row spends at most one under $u$), and opposing budgets $0<\beta_0<\beta$. Let $u'$ be an anchor table in $P(\gamma)$ for some $\gamma>\beta$, or the all-zero table if no tuple has score greater than $h^*$. Then every allocation specified by the label table spends at most one under $u'$, and
--   $$U_w(u';\beta)\le U_w(u;\beta_0)+m/S.$$
--   This is the payoff guarantee of the budget transfer of §5.3.
--
--   Differences from the source:
--   - generalization: the label table of the T-row lists of Lemma 5.6 → a label table with any number R ≥ 1 of rows; reason: the proof uses only that each label has probability 1/K; T rows are a special case
--   - reading: the normalized anchor table u of §5.3, whose rows spend at most one → u satisfies the static constraints: u_j0 = 0, nondecreasing in the label, entries ≤ 1, rows ≤ 1; reason: the anchors of §5.3 have these properties by construction (p. 40), and the text states u ∈ P(β₀) (p. 64)
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), p. 64, Lemma E.1

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_Anchors

open MeasureTheory

namespace BlottoFPTAS.Main

/-- **Lemma E.1** (Bichler, Ghosh, arXiv:2611.05221, held version sha256 cac3638e…, p. 64).
Fix `m ≥ 2` battlefields with positive values `w` summing to one, `e = 2^{-a}`, a label table in
which every label has probability `1/K` on every battlefield, an anchor table `u` satisfying the
static constraints (rows spend at most one), and opposing budgets `0 < β₀ < β`. Let `u′` be an
anchor table in `P(γ)` for some `γ > β`, or the all-zero table if no tuple has score greater than
`h*`. Then every row spends at most one under `u′`, and `U_w(u′; β) ≤ U_w(u; β₀) + m/S`. -/
theorem lemma_E_1 {m R : ℕ} (hm : 2 ≤ m) (a : ℕ) (ha : 1 ≤ a) (w : Fin m → ℝ)
    (hw : ∀ j, 0 < w j) (hsum : ∑ j, w j = 1) (hR : 0 < R)
    (lab : Fin R → Fin m → Fin (Klab a)) (hlab : EachLabelOneOverK a lab)
    (u : Fin m → Fin (Klab a) → ℝ) (hu : IsStatic a u lab) (β₀ β : ℝ) (hβ₀ : 0 < β₀)
    (hβ : β₀ < β) (u' : Fin m → Fin (Klab a) → ℝ)
    (hu' : (∃ γ : ℝ, β < γ ∧ InP a w u β₀ lab γ u') ∨
      ((∀ l : Fin m → Fin (Klab a), tupleScore a w l ≤ hStar a w u β₀) ∧ u' = 0)) :
    (∀ i, ∑ j, u' j (lab i j) ≤ 1) ∧
      U w (tableLaw a u' lab) β ≤ U w (tableLaw a u lab) β₀ + m / Sscore m a := by sorry

end BlottoFPTAS.Main
