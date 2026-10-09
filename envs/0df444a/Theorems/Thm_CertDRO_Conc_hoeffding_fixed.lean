-- Prove2me | Theorems.Thm_CertDRO_Conc_hoeffding_fixed
-- name    : CertDRO.Conc.hoeffding_fixed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:09:54.348843+00:00
-- url     : https://prove2.me/theorems/2c990877-86ce-4aed-89db-01fee186ad75
-- title:
--   §B.7 — Hoeffding at a fixed θ: P(|ρ̂ₙ(θ) − ρ(θ)| ≥ t/2) ≤ 2exp(−nt²/(8K²))
-- statement:
--   Let $Z\subseteq\mathbb R^m$, let $P_0$ be a probability measure on $\mathbb R^m$ with $P_0(Z)=1$, and let $Z_1,\dots,Z_n$ be i.i.d. with law $P_0$, with empirical distribution $\widehat P_n$. Fix a parameter $\theta$ and a map $T$, suppose $z\mapsto c(T(\theta;z),z)$ is $P_0$-measurable and $|c(T(\theta;z),z)|\le K$ for all $z\in Z$. Then for every $t>0$,
--   $$\mathbb P\Bigl(\bigl|\mathbb E_{\widehat P_n}[c(T(\theta;Z),Z)]-\mathbb E_{P_0}[c(T(\theta;Z),Z)]\bigr|\ge\tfrac t2\Bigr)\le2\exp\Bigl(-\frac{nt^2}{8K^2}\Bigr).$$
--   With $K=2L_cM_z$ (case (i) of Theorem 4) the exponent is the paper's $-nt^2/(32L_c^2M_z^2)$.
--
--   This is the fixed-parameter concentration that the union bound over a cover of $\Theta$ upgrades to the uniform bound.
--
--   **Formalization Note** The sample is the coordinate process on $(\mathbb R^m)^n$ under the product measure $P_0^{\otimes n}$. The bound $K$ is stated directly as a hypothesis (it is supplied by the cost bounds of §B.7), so this item covers case (ii), where $K=M_\ell/\gamma$, by the same formula. When $n=0$ the empirical mean is $0$ and the bound is trivial.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 44, §B.7, display after "Applying Hoeffding's inequality"

import Definitions.Def_CertDRO_Conc_model

namespace CertDRO.Conc

open MeasureTheory

/-- §B.7, p. 44, Hoeffding's inequality at a fixed parameter: if `Z₁, …, Zₙ` are i.i.d. with law
`P₀` (carried by `Z`), `z ↦ c(T(θ; z), z)` is measurable and `|c(T(θ; z), z)| ≤ K` on `Z`, then for
every `t > 0`
`P(|E_{P̂ₙ}[c(T(θ; Z), Z)] − E_{P₀}[c(T(θ; Z), Z)]| ≥ t/2) ≤ 2 exp(−n t² / (8 K²))`.
With `K = 2 Lc Mz` the exponent is the printed `−n t² / (32 Lc² Mz²)`. -/
theorem hoeffding_fixed {d m n : ℕ} (Z : Set (CertDRO.SGD.Data m)) (c : CertDRO.SGD.Data m → CertDRO.SGD.Data m → ℝ)
    (T : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Data m) (P₀ : Measure (CertDRO.SGD.Data m)) [IsProbabilityMeasure P₀]
    (θ : CertDRO.SGD.Param d) (K t : ℝ) (ht : 0 < t)
    (hP₀ : P₀ Zᶜ = 0) (hmeas : AEMeasurable (fun z => c (T θ z) z) P₀)
    (hK : ∀ z ∈ Z, |c (T θ z) z| ≤ K) :
    (Measure.pi fun _ : Fin n => P₀) {ω | t / 2 ≤ deviation T c P₀ ω θ} ≤
      2 * ENNReal.ofReal (Real.exp (-(n : ℝ) * t ^ 2 / (8 * K ^ 2))) := by sorry

end CertDRO.Conc
