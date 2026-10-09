-- Prove2me | Theorems.Thm_CertDRO_Conc_tail_bound
-- name    : CertDRO.Conc.tail_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:09:20.709933+00:00
-- url     : https://prove2.me/theorems/1ca32d4f-c067-4dc4-9de1-2136d3b03ff5
-- title:
--   §B.7 — P(sup_Θ |ρ̂ₙ(θ) − ρ(θ)| ≥ t) ≤ 2N(Θ, (γ − L_zz)t/(4L_cL_zθ), ‖·‖) exp(−nt²/(8K²))
-- statement:
--   This is the uniform concentration of the robustness level proved in Section B.7 (the tail bound from which Theorem 4 is read off), in both cases (i) and (ii).
--
--   Let $Z\subseteq\{z\in\mathbb R^m:\|z\|_2\le M_z\}$ be convex and let $\Theta\subseteq\mathbb R^d$ be an arbitrary set. Let the cost $c$ satisfy Assumption A, the loss $\ell$ satisfy Assumption B on $\Theta\times Z$ with constants $L_{\theta\theta},L_{zz},L_{\theta z},L_{z\theta}$, and let $\gamma>L_{zz}$, $L_c>0$, $L_{z\theta}>0$. Let $T$ be the transportation map, $T(\theta;z_0)\in\operatorname{argmax}_{z\in Z}\{\ell(\theta;z)-\gamma c(z,z_0)\}$ for $\theta\in\Theta$, $z_0\in Z$. Let $P_0$ be a probability measure with $P_0(Z)=1$, let $Z_1,\dots,Z_n$ be i.i.d. $\sim P_0$ with empirical distribution $\widehat P_n$, and assume $z\mapsto c(T(\theta;z),z)$ is $P_0$-measurable for every $\theta\in\Theta$. Let $K$ be given by
--   1. case (i): $c$ is $L_c$-Lipschitz over $Z$ in each argument, and $K=2L_cM_z$; or
--   2. case (ii): for every $\theta\in\Theta$, $\ell(\theta;z)\in[0,M_\ell]$ on $Z$ and $z\mapsto\ell(\theta;z)$ is $\gamma L_c$-Lipschitz on $Z$, and $K=M_\ell/\gamma$.
--
--   Then for every $t>0$,
--   $$\mathbb P\Bigl(\sup_{\theta\in\Theta}\bigl|\mathbb E_{\widehat P_n}[c(T(\theta;Z),Z)]-\mathbb E_{P_0}[c(T(\theta;Z),Z)]\bigr|\ge t\Bigr)\le 2\,N\Bigl(\Theta,\frac{(\gamma-L_{zz})\,t}{4L_cL_{z\theta}},\|\cdot\|_2\Bigr)\exp\Bigl(-\frac{nt^2}{8K^2}\Bigr),$$
--   where $N(V,\epsilon,\|\cdot\|)$ is the least number of points $\theta_1,\dots,\theta_N$ of $V$ whose closed $\epsilon$-balls cover $V$, and $+\infty$ if no finite cover exists. In case (i), $8K^2=32L_c^2M_z^2$ and the bound is exactly the paper's display.
--
--   The result shows that the robustness level $\widehat\rho_n(\theta)$ certified on the training sample generalizes to the population uniformly over the parameter set, with the usual dependence on its covering number.
--
--   **Formalization Note** The supremum is a real supremum over $\Theta$ of quantities bounded by $2K$, hence the true supremum; for $\Theta=\emptyset$ it is $0$, the event is empty and $N=0$. The event need not be measurable: $\mathbb P$ of it is the outer measure of the product measure $P_0^{\otimes n}$. The covering number is Mathlib's `Metric.coveringNumber` (values in $\mathbb N\cup\{\infty\}$), with centres in $\Theta$. The definition on p. 9 does not say where the centres lie, but the paper's loss is $\ell:\Theta\times Z\to\mathbb R$ and its proof applies Hoeffding's inequality "for any fixed $\theta\in\Theta$" at the centres, so the centres are points of $\Theta$. The radius is positive under the hypotheses. Added explicitly: $\gamma>L_{zz}$ (so $[\gamma-L_{zz}]_+=\gamma-L_{zz}$), $L_c>0$ and $L_{z\theta}>0$ (the radius divides by $4L_cL_{z\theta}$), convexity of $Z$, and measurability of $z\mapsto c(T(\theta;z),z)$ for $\theta\in\Theta$. Assumption B, the transportation map and case (ii) are required on $\Theta$ only, as in Theorem 4. The paper's printed Theorem 4, (17), is not claimed: it does not follow from this tail bound as printed.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 44, §B.7, last display of the proof of Theorem 4 and the following paragraph (case (ii)); Theorem 4, p. 11; covering number, p. 9

import Definitions.Def_CertDRO_Conc_model

namespace CertDRO.Conc

open MeasureTheory

/-- §B.7, last display of the proof of Theorem 4, p. 44 (cases (i) and (ii)): let
`Z ⊆ {z ∈ ℝ^m : ‖z‖ ≤ Mz}` be convex, let Assumptions A and B hold on `Θ × Z` with `γ > Lzz`, let
`T` be the transportation map (9) on `Θ`, and let `Z₁, …, Zₙ` be i.i.d. with law `P₀` carried by `Z`.
Under case (i) put `K = 2 Lc Mz`; under case (ii) (for `θ ∈ Θ`, as in Theorem 4) put `K = Mℓ / γ`.
Then for every `t > 0`
`P(sup_{θ ∈ Θ} |E_{P̂ₙ}[c(T(θ; Z), Z)] − E_{P₀}[c(T(θ; Z), Z)]| ≥ t)
   ≤ 2 N(Θ, (γ − Lzz) t / (4 Lc Lzθ), ‖·‖) exp(−n t² / (8 K²))`,
where `N` is the covering number of `Θ` in the ℓ²-norm by centres `θ₁, …, θ_N ∈ Θ` (the proof applies
Hoeffding's inequality "for any fixed θ ∈ Θ" at the centres). In case (i), `8 K² = 32 Lc² Mz²`. -/
theorem tail_bound {d m n : ℕ} (Z : Set (CertDRO.SGD.Data m)) (hZ : Convex ℝ Z) (Θ : Set (CertDRO.SGD.Param d))
    (ℓ : CertDRO.SGD.Param d → CertDRO.SGD.Data m → ℝ) (gθ : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Param d)
    (gz : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Data m) (c : CertDRO.SGD.Data m → CertDRO.SGD.Data m → ℝ) (T : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Data m)
    (P₀ : Measure (CertDRO.SGD.Data m)) [IsProbabilityMeasure P₀]
    (Lθθ Lzz Lθz Lzθ γ Lc Mℓ Mz K t : ℝ)
    (hZbdd : ∀ z ∈ Z, ‖z‖ ≤ Mz)
    (hA : CertDRO.SGD.AssumptionA Z c) (hB : AssumptionB Θ Z ℓ gθ gz Lθθ Lzz Lθz Lzθ)
    (hγ : Lzz < γ) (hLc : 0 < Lc) (hLzθ : 0 < Lzθ) (ht : 0 < t)
    (hT : IsTransportMap Θ Z ℓ c γ T)
    (hP₀ : P₀ Zᶜ = 0) (hmeas : ∀ θ ∈ Θ, AEMeasurable (fun z => c (T θ z) z) P₀)
    (hcase : (CaseI Z c Lc ∧ K = 2 * Lc * Mz) ∨ (CaseII Θ Z ℓ γ Lc Mℓ ∧ K = Mℓ / γ)) :
    (Measure.pi fun _ : Fin n => P₀) {ω | t ≤ ⨆ θ : Θ, deviation T c P₀ ω θ} ≤
      2 * (Metric.coveringNumber (Real.toNNReal ((γ - Lzz) * t / (4 * Lc * Lzθ))) Θ : ENNReal) *
        ENNReal.ofReal (Real.exp (-(n : ℝ) * t ^ 2 / (8 * K ^ 2))) := by sorry

end CertDRO.Conc
