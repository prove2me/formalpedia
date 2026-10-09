-- Prove2me | Theorems.Thm_CertDRO_Conc_deviation_lipschitz
-- name    : CertDRO.Conc.deviation_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:09:43.595613+00:00
-- url     : https://prove2.me/theorems/724a41d0-90a9-4e61-802e-27ef25f4fc4c
-- title:
--   §B.7 — θ ↦ |E_P̂ₙ[c(T(θ;Z),Z)] − E_P₀[c(T(θ;Z),Z)]| is 2L_cL_zθ/(γ − L_zz)-Lipschitz on Θ
-- statement:
--   Let $Z\subseteq\{z\in\mathbb R^m:\|z\|_2\le M_z\}$ be convex and $\Theta\subseteq\mathbb R^d$. Let $c$ satisfy Assumption A, $\ell$ satisfy Assumption B on $\Theta\times Z$, $\gamma>L_{zz}$, let $T$ be a transportation map on $\Theta$, and assume case (i) or case (ii) of Theorem 4 (case (ii) for the parameters in $\Theta$). Let $P_0$ be a probability measure on $\mathbb R^m$ with $P_0(Z)=1$ such that $z\mapsto c(T(\theta;z),z)$ is $P_0$-measurable for each $\theta\in\Theta$. Fix a sample $\omega=(Z_1,\dots,Z_n)\in Z^n$ with empirical distribution $\widehat P_n$ and write
--   $$D_n(\theta)=\Bigl|\mathbb E_{\widehat P_n}[c(T(\theta;Z),Z)]-\mathbb E_{P_0}[c(T(\theta;Z),Z)]\Bigr| .$$
--   Then for all $\theta_1,\theta_2\in\Theta$,
--   $$|D_n(\theta_1)-D_n(\theta_2)|\le\frac{2L_cL_{z\theta}}{\gamma-L_{zz}}\,\|\theta_1-\theta_2\|_2 .$$
--
--   This is the Lipschitz property of the empirical-minus-population deviation that lets a finite cover of $\Theta$ control its supremum.
--
--   **Formalization Note** The page prints "$c(T(\theta;Z),\theta)$" inside the empirical expectation; this is a typo for $c(T(\theta;Z),Z)$, and the intended statement is formalized. Measurability of $z\mapsto c(T(\theta;z),z)$ is the field's standing convention and is stated explicitly; together with the bound $\|z\|\le M_z$ (case (i)) or $\ell\in[0,M_\ell]$ (case (ii)) it makes the population expectation a genuine (finite) integral. $[\gamma-L_{zz}]_+$ is $\gamma-L_{zz}$.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 44, §B.7, first sentence after the proof of Lemma 5

import Definitions.Def_CertDRO_Conc_model

namespace CertDRO.Conc

open MeasureTheory

/-- §B.7, p. 44, first sentence after the proof of Lemma 5: for every sample `ω ∈ Zⁿ`, the map
`θ ↦ |E_{P̂ₙ}[c(T(θ; Z), Z)] − E_{P₀}[c(T(θ; Z), Z)]|` is `2 Lc Lzθ / (γ − Lzz)`-Lipschitz on `Θ`.
`P₀` is a probability measure carried by `Z`, and `z ↦ c(T(θ; z), z)` is `P₀`-a.e. measurable for
`θ ∈ Θ`. -/
theorem deviation_lipschitz {d m n : ℕ} (Z : Set (CertDRO.SGD.Data m)) (hZ : Convex ℝ Z) (Θ : Set (CertDRO.SGD.Param d))
    (ℓ : CertDRO.SGD.Param d → CertDRO.SGD.Data m → ℝ) (gθ : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Param d)
    (gz : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Data m) (c : CertDRO.SGD.Data m → CertDRO.SGD.Data m → ℝ) (T : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Data m)
    (P₀ : Measure (CertDRO.SGD.Data m)) [IsProbabilityMeasure P₀]
    (Lθθ Lzz Lθz Lzθ γ Lc Mℓ Mz : ℝ)
    (hZbdd : ∀ z ∈ Z, ‖z‖ ≤ Mz)
    (hA : CertDRO.SGD.AssumptionA Z c) (hB : AssumptionB Θ Z ℓ gθ gz Lθθ Lzz Lθz Lzθ)
    (hγ : Lzz < γ) (hT : IsTransportMap Θ Z ℓ c γ T)
    (hcase : CaseI Z c Lc ∨ CaseII Θ Z ℓ γ Lc Mℓ)
    (hP₀ : P₀ Zᶜ = 0) (hmeas : ∀ θ ∈ Θ, AEMeasurable (fun z => c (T θ z) z) P₀)
    (ω : Fin n → CertDRO.SGD.Data m) (hω : ∀ i, ω i ∈ Z) :
    ∀ θ₁ ∈ Θ, ∀ θ₂ ∈ Θ,
      |deviation T c P₀ ω θ₁ - deviation T c P₀ ω θ₂| ≤
        2 * Lc * Lzθ / (γ - Lzz) * ‖θ₁ - θ₂‖ := by sorry

end CertDRO.Conc
