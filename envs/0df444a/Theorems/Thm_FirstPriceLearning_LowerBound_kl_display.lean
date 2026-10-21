-- Prove2me | Theorems.Thm_FirstPriceLearning_LowerBound_kl_display
-- name    : FirstPriceLearning.LowerBound.kl_display
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T10:14:12.401731+00:00
-- url     : https://prove2.me/theorems/bbf52258-57ce-4543-a5e4-66563b89ccc0
-- title:
--   App. B, p. 37 — $D_{\mathrm{KL}}(P_1^{\otimes T}\|P_2^{\otimes T})=T\,D_{\mathrm{KL}}(G_1\|G_2)\le32T\Delta^2$
-- statement:
--   Let $\Delta\in(0,1/4)$ and $T\in\mathbb N$, let $G_1,G_2$ be the two HOB laws of the two-point construction, and let $P_i^{\otimes T}$ be the $T$-fold product of $G_i$. Then
--
--   $$
--   D_{\mathrm{KL}}\bigl(P_1^{\otimes T}\big\|P_2^{\otimes T}\bigr)=T\,D_{\mathrm{KL}}(G_1\|G_2)
--   =T\Bigl(\bigl(\tfrac12-\Delta\bigr)\log\frac{1/2-\Delta}{1/2+\Delta}+\bigl(\tfrac12+\Delta\bigr)\log\frac{1/2+\Delta}{1/2-\Delta}\Bigr)\le 32T\Delta^2 ,
--   $$
--
--   and also $D_{\mathrm{KL}}(P_2^{\otimes T}\|P_1^{\otimes T})\le32T\Delta^2$.
--
--   The bound shows that $T$ observations of the HOB carry only $O(T\Delta^2)$ information for telling $G_1$ from $G_2$; with $\Delta$ of order $1/\sqrt T$ the two hypotheses stay hard to distinguish.
--
--   **Formalization Note** Divergences are Mathlib's `klDiv`, valued in $[0,\infty]$; the closed form and the bound $32T\Delta^2$ are embedded with `ENNReal.ofReal`. The bound with the roles exchanged is not printed in the display; it is the second divergence that Lemma 12 needs, and it holds with the same closed form by the symmetry $G_1\leftrightarrow G_2$, $1/3\leftrightarrow2/3$. The two terms of the printed closed form appear in the order printed; their sum is $2\Delta\log\frac{1+2\Delta}{1-2\Delta}$.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 37, App. B, last display

import Mathlib
import Definitions.Def_FirstPriceLearning_LowerBound_TwoPointLaws

open MeasureTheory InformationTheory

namespace FirstPriceLearning.LowerBound

/-- arXiv:2003.09795v7, App. B, p. 37, last display: for `Δ ∈ (0, 1/4)` and every `T`,
`D_KL(P₁^{⊗T} ‖ P₂^{⊗T}) = T·D_KL(G₁‖G₂)`, `D_KL(G₁‖G₂) = (1/2 − Δ) log((1/2 − Δ)/(1/2 + Δ))
+ (1/2 + Δ) log((1/2 + Δ)/(1/2 − Δ))`, and `D_KL(P₁^{⊗T} ‖ P₂^{⊗T}) ≤ 32TΔ²`; the same bound holds
with the roles of `G₁` and `G₂` exchanged (used with Lemma 12). -/
theorem kl_display (T : ℕ) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1 / 4) :
    klDiv (Measure.pi fun _ : Fin T => lawG1 Δ) (Measure.pi fun _ : Fin T => lawG2 Δ) =
        (T : ENNReal) * klDiv (lawG1 Δ) (lawG2 Δ) ∧
    klDiv (lawG1 Δ) (lawG2 Δ) =
        ENNReal.ofReal ((1 / 2 - Δ) * Real.log ((1 / 2 - Δ) / (1 / 2 + Δ))
          + (1 / 2 + Δ) * Real.log ((1 / 2 + Δ) / (1 / 2 - Δ))) ∧
    klDiv (Measure.pi fun _ : Fin T => lawG1 Δ) (Measure.pi fun _ : Fin T => lawG2 Δ) ≤
        ENNReal.ofReal (32 * T * Δ ^ 2) ∧
    klDiv (Measure.pi fun _ : Fin T => lawG2 Δ) (Measure.pi fun _ : Fin T => lawG1 Δ) ≤
        ENNReal.ofReal (32 * T * Δ ^ 2) := by sorry

end FirstPriceLearning.LowerBound
