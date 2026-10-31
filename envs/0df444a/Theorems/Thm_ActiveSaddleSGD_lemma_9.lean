-- Prove2me | Theorems.Thm_ActiveSaddleSGD_lemma_9
-- name    : ActiveSaddleSGD.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:44.818925+00:00
-- url     : https://prove2.me/theorems/0931f80d-144a-4efe-940e-628be5e38c2b
-- title:
--   Lemma 9 — the recursion for $w_n^-$ with noise $e$ and perturbations $r$, $\tilde r$
-- statement:
--   Under the assumptions of Lemma 8, with $G$ as in Proposition 6 and Remark 5, the adapted sequence $w_n^-=y_n^--G(y_n^+)$ is given by
--   $$
--   w_{n+1}^-=w_n^-+\gamma_nH_nw_n^-+\gamma_n(e_{n+1}+r_{n+1}+\tilde r_{n+1}),
--   $$
--   where $(e_n)$, $(r_n)$, $(\tilde r_n)$ are $\mathbb R^{d^-}$-valued, $(H_n)$ is $\mathbb R^{d^-\times d^-}$-valued, and all are adapted. There are constants $C_\times>0$ and constants $c_\times>0$ as small as needed such that, with probability one: $\|H_n+J^-\|\le c_H$; $\mathbb E_ne_{n+1}=0$; $\sup\mathbb E_n\|e_{n+1}\|^4\le C_{e,1}$; $\inf\mathbb E_n\|e_{n+1}\|\ge C_{e,2}$; $\sum_i\|r_{i+1}\|^2\le c_r$; $\sup\mathbb E_n\|\tilde r_{n+1}\|^4\le C_{\tilde r}$; $\sup\mathbb E_n\|\tilde r_{n+1}\|^2\le c_{\tilde r,1}$; and $\sup\chi_n^{-1/2}\mathbb E_n[\sum_{i\ge n}\gamma_i\|\tilde r_{i+1}\|]\le c_{\tilde r,2}$.
--
--   This reduces the avoidance of the graph to the repulsion of a single norm.
--
--   **Formalization Note** The data of Lemma 8 are hypotheses: the bound $C_D$ on $\tilde D$, the bound $c_F$ on $\Delta$, and the bounds of `RepulsionBounds` on $\tilde\eta$, $\varrho$, $\tilde\varrho$, $\|J_G\|\le c_G$. The constants $C_{e,1}$, $C_{e,2}$, $C_{\tilde r}$ come first, and for any targets $c_H$, $c_r$, $c_{\tilde r,1}$, $c_{\tilde r,2}$ there are thresholds on the data of Lemma 8.
--
--   Differences from the source:
--   - reading: "constants $c_\times$ as small as needed"; the proof puts the Taylor remainder $\xi/\gamma_n$ in $r$ → thresholds that may depend on $(\gamma_n)$ and on a bound $C_{G,2}$ on the second derivative of $G$; $e$, $r$, $\tilde r$ are only required to exist; reason: with unbounded $\tilde\eta$, $\xi/\gamma_n$ is unbounded, so the almost sure bound v) fails for the printed $r$; it is at most $\min(C\gamma_nh^2,2c_Gh)$ for the increment $h$, so it can go in $\tilde r$, where viii) requires that dependence
--   - reading: "see Remark 5" for $\|\xi\|\le C\|y_{n+1}^+-y_n^+\|^2$ → the hypothesis $\|D^2G\|\le C_{G,2}$, with $G$ of class $C^2$ on $\mathbb R^{d^+}$; reason: that is the bound the page uses, and the smooth cutoff of Remark 5 provides it
--   - reading: Lemma 8 ii) and $F(w_n)=H_nw_n^-$ → the bound on $\Delta$ and the identity of Lemma 7 on the whole space; reason: the proof uses them at every $w_n$; that is what "the approximation provided by Lemma 7 satisfies $\sup_w$" means after the reduction of Lemma 8
--   - reading: "all are adapted" → the hypothesis that $R$ is measurable; reason: adaptedness of $H_n$ needs it, and $D$ is continuous in the application
--   - encoding: $y_n$, $\tilde\eta_n$, $\varrho_n$, $\tilde\varrho_n$ in $\mathbb R^d$ → their images under $P^{-1}$ in $\mathbb R^{d^+}\times\mathbb R^{d^-}$, with the bounds stated there; reason: the page's constants change by factors depending only on $P$
-- source:
--   Bianchi, Hachem & Schechtman, Stochastic Subgradient Descent Escapes Active Strict Saddles on Weakly Convex Functions, arXiv:2108.02072v4, Lemma 9, p.27, with Lemma 8, pp.26–27, and Remark 5, p.26

import Mathlib
import Definitions.Def_ActiveSaddleSGD_ProjectedIterates
import Definitions.Def_ActiveSaddleSGD_CenterStable
import Definitions.Def_ActiveSaddleSGD_Repulsive

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ActiveSaddleSGD

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Lemma 9, p.27: under the assumptions of Lemma 8,
pp.26–27, the adapted sequence `w_n⁻ = y_n⁻ − G(y_n⁺)` satisfies
`w_{n+1}⁻ = w_n⁻ + γ_n H_n w_n⁻ + γ_n (e_{n+1} + r_{n+1} + r̃_{n+1})`, with `(e_n)`, `(r_n)`, `(r̃_n)`, `(H_n)`
adapted, and constants `C_·` and constants `c_·` as small as needed such that almost surely
i) `‖H_n + J⁻‖ ≤ c_H` and ii)–viii) of `RepulsionBounds`.

**Formalization Note** The recursion is in the basis of `P`: `y`, `η̃`, `ϱ`, `ϱ̃` are the page's `P⁻¹y_n`, ….
"As small as needed" reads: the constants `C_e`, `C_r̃` come first, then for any targets `c_H`, `c_r`,
`c_{r̃,1}`, `c_{r̃,2}` there are thresholds `c_F`, `c_ρ`, `c_{ρ̃,1}`, `c_{ρ̃,2}`, `c_G` for the data of Lemma 8.
The thresholds may depend on `(γ_n)` and on `CG2`, the bound on the second derivative of `G` behind
"see Remark 5" (p.28). The reason is the page's Taylor remainder `ξ/γ_n`: it is at most
`min(C γ_n h², 2 c_G h)` with `h` the increment, which is unbounded with `η̃`, so it cannot be in `r` with
the almost sure bound v), and it goes in `r̃`, where viii) needs that dependence. `e`, `r`, `r̃` are only
required to exist. `R` is measurable: Lemma 9's claim that `H_n` is adapted needs it, and `D` is
continuous in the application. `Δ` is the function of Lemma 7 with Lemma 8 ii): the bound and the
identity hold on the whole space, as the proof of Lemma 9 uses them at `w_n`. -/
theorem lemma_9.{v} {dp dm : ℕ} (Jp : Matrix (Fin dp) (Fin dp) ℝ)
    (Jm : Matrix (Fin dm) (Fin dm) ℝ)
    (R : EuclideanSpace ℝ (Fin dp) × EuclideanSpace ℝ (Fin dm) →
      EuclideanSpace ℝ (Fin dp) × EuclideanSpace ℝ (Fin dm))
    (hsys : IsBlockSystem Jp Jm R) (hRm : Measurable R)
    (γ : ℕ → ℝ) (hγ : IsStepSequence γ)
    (CD Cη1 Cη2 Cρt CG2 : ℝ) (hCD : 0 < CD) (hCη1 : 0 < Cη1) (hCη2 : 0 < Cη2) (hCρt : 0 < Cρt)
    (hCG2 : 0 < CG2) :
    ∃ Ce1 Ce2 Crt : ℝ, 0 < Ce1 ∧ 0 < Ce2 ∧ 0 < Crt ∧
      ∀ cH cr cr1 cr2 : ℝ, 0 < cH → 0 < cr → 0 < cr1 → 0 < cr2 →
      ∃ cF cρ cρ1 cρ2 cG : ℝ, 0 < cF ∧ 0 < cρ ∧ 0 < cρ1 ∧ 0 < cρ2 ∧ 0 < cG ∧
        ∀ (Ω : Type v) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
          (ℱ : Filtration ℕ mΩ) (𝒰 : Set (EuclideanSpace ℝ (Fin dp)))
          (G : EuclideanSpace ℝ (Fin dp) → EuclideanSpace ℝ (Fin dm))
          (Δ : EuclideanSpace ℝ (Fin dp) × EuclideanSpace ℝ (Fin dm) →
            Matrix (Fin dm) (Fin dm) ℝ)
          (y ηt ρ ρt : ℕ → Ω → EuclideanSpace ℝ (Fin dp) × EuclideanSpace ℝ (Fin dm)),
          IsCenterStableGraph Jp Jm R 𝒰 G → ContDiff ℝ 2 G →
          (∀ u, ‖fderiv ℝ G u‖ ≤ cG) → (∀ u, ‖fderiv ℝ (fderiv ℝ G) u‖ ≤ CG2) →
          (∀ q, ‖blockField Jp Jm R q‖ ≤ CD) →
          (∀ q, ‖matCLM (Δ q)‖ ≤ cF) →
          (∀ q, graphDefect Jp Jm R G q = matCLM (-Jm + Δ q) q.2) →
          StronglyAdapted ℱ y → StronglyAdapted ℱ ηt → StronglyAdapted ℱ ρ →
          StronglyAdapted ℱ ρt →
          (∀ n ω, y (n + 1) ω = y n ω - γ n • blockField Jp Jm R (y n ω) + γ n • ηt (n + 1) ω
            + γ n • ρ (n + 1) ω + γ n • ρt (n + 1) ω) →
          RepulsionBounds μ ℱ γ ηt (fun n ω => (ηt n ω).2) ρ ρt Cη1 Cη2 cρ Cρt cρ1 cρ2 →
          ∃ (H : ℕ → Ω → Matrix (Fin dm) (Fin dm) ℝ)
            (e r rt : ℕ → Ω → EuclideanSpace ℝ (Fin dm)),
            StronglyAdapted ℱ H ∧ StronglyAdapted ℱ e ∧ StronglyAdapted ℱ r ∧
            StronglyAdapted ℱ rt ∧
            (∀ n ω, (y (n + 1) ω).2 - G (y (n + 1) ω).1 =
              (y n ω).2 - G (y n ω).1 + γ n • matCLM (H n ω) ((y n ω).2 - G (y n ω).1) +
                γ n • (e (n + 1) ω + r (n + 1) ω + rt (n + 1) ω)) ∧
            (∀ᵐ ω ∂μ, ∀ n, ‖matCLM (H n ω + Jm)‖ ≤ cH) ∧
            RepulsionBounds μ ℱ γ e e r rt Ce1 Ce2 cr Crt cr1 cr2 := by sorry

end ActiveSaddleSGD
