-- Prove2me | Theorems.Thm_AffinePSD_InfDiv_lemma_5_10
-- name    : AffinePSD.InfDiv.lemma_5_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:32.427196+00:00
-- url     : https://prove2.me/theorems/78d98c4d-2d87-4547-8d7b-8dc1c628bf96
-- title:
--   Lemma 5.10 — $\mathcal C,\mathcal C^S$ are convex cones closed under composition and limits; $R^\delta\to R$ locally uniformly
-- statement:
--   Let $\mathcal C$ and $\mathcal C^S$ be the sets of §5.3 (Lévy–Khintchine exponents plus a nonnegative constant, and their matrix-valued analogues). Then:
--
--   1. $\mathcal C$ and $\mathcal C^S$ are convex cones in $C(S_d^+)$.
--   2. $\varphi\in\mathcal C$ and $\psi\in\mathcal C^S$ imply $\varphi(\psi)\in\mathcal C$.
--   3. $\psi,\psi_1\in\mathcal C^S$ imply $\psi_1(\psi)\in\mathcal C^S$.
--   4. If $\varphi_k\in\mathcal C$ converges to a continuous function $\varphi$ on $S_d^+$, then $\varphi\in\mathcal C$. The same holds for sequences in $\mathcal C^S$.
--   5. Let $(\alpha=0,b,\beta^{ij},c,\gamma,m,\mu)$ be an admissible parameter set. Then
--   $$R^\delta\to R\quad\text{locally uniformly on }S_d^+\text{ as }\delta\to0,$$
--   where $R^\delta$ corresponds to the parameter set $(\alpha=0,b,\beta^{ij},c,\gamma,m,\mu\mathbf 1_{\{\|\xi\|\ge\delta\}})$, with the same truncation function.
--
--   These closure properties carry the Picard iteration of Proposition 5.11, and item 5 reduces that proposition to jump measures of finite first moment.
--
--   **Formalization Note** Functions live on $M_d$ and are constrained on $S_d^+$ only, and "in $C(S_d^+)$" means continuous on $S_d^+$. A convex cone is closed under addition and under multiplication by $a>0$. The paper does not say how $\varphi_k$ converges in item 4; it is read as pointwise convergence on $S_d^+$, which is what the Picard iterates of Proposition 5.11 give. In item 5, $\mu\mathbf 1_{\{\|\xi\|\ge\delta\}}$ is $\nu$ restricted to $\{\|\xi\|\ge\delta\}$ with the same density $H$ (the $\mu\mapsto(\nu,H)$ encoding). $\|\cdot\|$ is the trace norm, and $\delta\to0$ means $\delta\downarrow0$. Local uniform convergence on $S_d^+$ does not depend on the norm chosen on $M_d$.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), §5.3, Lemma 5.10, pp. 50–51

import Mathlib
import Definitions.Def_AffinePSD_InfDiv_Cone
import Definitions.Def_AffinePSD_Necessity_Params
import Definitions.Def_AffinePSD_InfDiv_LevyKhintchine

open MeasureTheory Filter Topology

namespace AffinePSD.InfDiv

/-- Lemma 5.10 (arXiv:0910.0137v3, §5.3, pp. 50–51).
(i) `C`, `C^S` are convex cones in `C(S_d^+)`.
(ii) `φ ∈ C`, `ψ ∈ C^S` imply `φ(ψ) ∈ C`.
(iii) `ψ, ψ_1 ∈ C^S` imply `ψ_1(ψ) ∈ C^S`.
(iv) If `φ_k ∈ C` converges to a continuous function `φ` on `S_d^+`, then `φ ∈ C`; similarly for
sequences in `C^S`.
(v) If `(α = 0, b, β^{ij}, c, γ, m, μ)` is admissible, then `R^δ → R` locally uniformly on `S_d^+`
as `δ → 0`, where `R^δ` corresponds to `(α = 0, b, β^{ij}, c, γ, m, μ 1_{‖ξ‖ ≥ δ})` (one fixed
truncation function `χ`).
Formalization Note: functions live on `Mat d` and are constrained on `S_d^+` only; "continuous" is
`ContinuousOn` `S_d^+`; a convex cone is closed under addition and multiplication by `a > 0`.
"Converges" in (iv) is read pointwise on `S_d^+`. In (v), `μ 1_{‖ξ‖≥δ}` is `ν` restricted to
`{‖ξ‖ ≥ δ}` with the same density `H` (the `μ ↦ (ν, H)` encoding), `‖·‖` is the trace norm
`fnorm`, `δ → 0` is `δ ↓ 0`, and local uniform convergence on `S_d^+` does not depend on the norm
of `M_d`. -/
theorem lemma_5_10 {d : ℕ} :
    -- (i)
    ((∀ φ ∈ CC d, ContinuousOn φ {u | AffinePSD.Necessity.PSD u}) ∧
      (∀ φ₁ ∈ CC d, ∀ φ₂ ∈ CC d, φ₁ + φ₂ ∈ CC d) ∧ (∀ φ ∈ CC d, ∀ a : ℝ, 0 < a → a • φ ∈ CC d) ∧
      (∀ ψ ∈ CS d, ContinuousOn ψ {u | AffinePSD.Necessity.PSD u}) ∧
      (∀ ψ₁ ∈ CS d, ∀ ψ₂ ∈ CS d, ψ₁ + ψ₂ ∈ CS d) ∧ (∀ ψ ∈ CS d, ∀ a : ℝ, 0 < a → a • ψ ∈ CS d)) ∧
    -- (ii)
    (∀ φ ∈ CC d, ∀ ψ ∈ CS d, φ ∘ ψ ∈ CC d) ∧
    -- (iii)
    (∀ ψ ∈ CS d, ∀ ψ₁ ∈ CS d, ψ₁ ∘ ψ ∈ CS d) ∧
    -- (iv)
    (∀ (φs : ℕ → AffinePSD.Necessity.Mat d → ℝ) (φ : AffinePSD.Necessity.Mat d → ℝ), (∀ k, φs k ∈ CC d) → ContinuousOn φ {u | AffinePSD.Necessity.PSD u} →
        (∀ u, AffinePSD.Necessity.PSD u → Tendsto (fun k => φs k u) atTop (𝓝 (φ u))) → φ ∈ CC d) ∧
    (∀ (ψs : ℕ → AffinePSD.Necessity.Mat d → AffinePSD.Necessity.Mat d) (ψ : AffinePSD.Necessity.Mat d → AffinePSD.Necessity.Mat d), (∀ k, ψs k ∈ CS d) →
        ContinuousOn ψ {u | AffinePSD.Necessity.PSD u} →
        (∀ u, AffinePSD.Necessity.PSD u → Tendsto (fun k => ψs k u) atTop (𝓝 (ψ u))) → ψ ∈ CS d) ∧
    -- (v)
    (∀ (χ : AffinePSD.Necessity.Trunc d) (P : AffinePSD.Necessity.Params d), AffinePSD.Necessity.Admissible χ P → P.α = 0 →
      TendstoLocallyUniformlyOn
        (fun (δ : ℝ) (u : AffinePSD.Necessity.Mat d) => AffinePSD.Necessity.Rpar χ { P with ν := P.ν.restrict {ξ | δ ≤ AffinePSD.Necessity.fnorm ξ.1} } u)
        (AffinePSD.Necessity.Rpar χ P) (𝓝[>] 0) {u | AffinePSD.Necessity.PSD u}) := by sorry

end AffinePSD.InfDiv
