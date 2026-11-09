-- Prove2me | Theorems.Thm_AutobidSPPE_lemma_2_13
-- name    : AutobidSPPE.lemma_2_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:59:38.46821+00:00
-- url     : https://prove2.me/theorems/048c3d66-887a-4467-8d1f-6760a15f25d6
-- title:
--   Lemma 2.13 — quantitative principal minors on spending rows
-- statement:
--   Throughout, $n\ge2$ bidders have independent values $v_i\sim\mathrm{Unif}[0,\bar v_i]$ with $0<\bar v_i\le\hat v_i<\infty$ (true supports $\bar v$, certified upper bounds $\hat v$), and budgets $\rho_i>0$; the constants of (10)–(12) are computed from $\hat v$ and $\rho$. At any $y\in\mathcal Y$ let
--   $$
--   M=\mathrm{diag}\big(\mathsf s_i(y)^{-1}\big)\,J_s\,\mathrm{diag}(y_i).
--   $$
--   1. Every row satisfies
--   $$
--   1-\sum_{j\ne i}(M_{ij})_+ = M_{ii}-\sum_{j\ne i}(-M_{ij})_+\ \ge\ \frac{\mathsf s_i(y)}{y_i}. \tag{32}
--   $$
--   2. If a nonempty index set $I$ has $\mathsf s_i(y)\ge\rho_{\min}/2$ for all $i\in I$, then
--   $$
--   \det M_{II}\ge\varrho^{|I|},\qquad \det (J_s)_{II}\ge\varrho^{2|I|}. \tag{33}
--   $$
--
--   These quantitative minor bounds give the uniform constants $L_p$ and $a$.
--
--   Differences from the source: none.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Lemma 2.13, (32)–(33), p.18

import Mathlib
import Definitions.Def_AutobidSPPE_endpointSpend
import Definitions.Def_AutobidSPPE_endpointBox
import Definitions.Def_AutobidSPPE_spendJac
import Definitions.Def_AutobidSPPE_rhoMin
import Definitions.Def_AutobidSPPE_varrho

namespace AutobidSPPE

/-- Lemma 2.13, p.18 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6)): at any `y ∈ 𝒴`, with `M = diag(𝗌ᵢ(y)⁻¹) J_s diag(yᵢ)`, every row
satisfies `1 − ∑_{j≠i}(Mᵢⱼ)₊ = Mᵢᵢ − ∑_{j≠i}(−Mᵢⱼ)₊ ≥ 𝗌ᵢ(y)/yᵢ` (32); and if a nonempty index
set `I` has `𝗌ᵢ(y) ≥ ρ_min/2` for all `i ∈ I`, then `det M_{II} ≥ ϱ^{|I|}` and
`det (J_s)_{II} ≥ ϱ^{2|I|}` (33).

**Formalization Note** `ϱ = min{1/4, ρ_min/(2U)}` of (10); principal submatrices are indexed by
the subtype of `I`. -/
theorem lemma_2_13 {n : ℕ} (hn : 2 ≤ n) (vbar vhat ρ : Fin n → ℝ) (hvbar : ∀ i, 0 < vbar i ∧ vbar i ≤ vhat i)
    (hρ : ∀ i, 0 < ρ i) :
    ∀ y ∈ endpointBox vbar ρ,
      let M : Matrix (Fin n) (Fin n) ℝ :=
        Matrix.diagonal (fun i => (endpointSpend y i)⁻¹) * spendJac y * Matrix.diagonal y
      (∀ i : Fin n,
        1 - ∑ j ∈ Finset.univ.erase i, max (M i j) 0 =
          M i i - ∑ j ∈ Finset.univ.erase i, max (-M i j) 0 ∧
        endpointSpend y i / y i ≤ M i i - ∑ j ∈ Finset.univ.erase i, max (-M i j) 0) ∧
      ∀ I : Finset (Fin n), I.Nonempty → (∀ i ∈ I, rhoMin ρ / 2 ≤ endpointSpend y i) →
        varrho vhat ρ ^ I.card ≤
          (M.submatrix (fun x : I => (x : Fin n)) (fun x : I => (x : Fin n))).det ∧
        varrho vhat ρ ^ (2 * I.card) ≤
          ((spendJac y).submatrix (fun x : I => (x : Fin n)) (fun x : I => (x : Fin n))).det := by sorry

end AutobidSPPE
