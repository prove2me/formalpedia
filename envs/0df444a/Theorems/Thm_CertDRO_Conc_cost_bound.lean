-- Prove2me | Theorems.Thm_CertDRO_Conc_cost_bound
-- name    : CertDRO.Conc.cost_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:09:20.98205+00:00
-- url     : https://prove2.me/theorems/cf14f395-f2e5-4137-bfdd-080ca490ff3d
-- title:
--   §B.7 — 0 ≤ c(T(θ; z), z) ≤ 2L_cM_z in case (i) and ≤ M_ℓ/γ in case (ii)
-- statement:
--   Let $Z\subseteq\{z\in\mathbb R^m:\|z\|_2\le M_z\}$ and $\Theta\subseteq\mathbb R^d$. Let $c$ satisfy Assumption A, let $\ell$ satisfy Assumption B on $\Theta\times Z$ (so $L_{zz}\ge0$), let $\gamma>L_{zz}$, and let $T$ be a transportation map on $\Theta$. Let $K$ be given by one of the two cases of Theorem 4:
--   1. case (i), $c$ is $L_c$-Lipschitz over $Z$ in each argument, and $K=2L_cM_z$;
--   2. case (ii) for the parameters in $\Theta$, and $K=M_\ell/\gamma$.
--
--   Then for every $\theta\in\Theta$ and $z\in Z$,
--   $$0\le c(T(\theta;z),z)\le K .$$
--
--   These bounds make the transported cost a bounded random variable, which is what Hoeffding's inequality needs at each fixed parameter.
--
--   **Formalization Note** The paper states $|c(T(\theta;Z),Z)|\le K$; since $c\ge0$ this is the stated two-sided bound. In case (ii) the paper's displayed middle step "$\gamma c(T(\theta;z),z)\le\ell(\theta;z)$" is loose; the conclusion $\gamma c(T(\theta;z),z)\le M_\ell$ follows from the argmax property, $c(z,z)=0$ and $0\le\ell\le M_\ell$, and only the conclusion is formalized.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 44, §B.7 (case (i): "|c(T(θ; Z), Z)| ≤ 2LcMz"; case (ii): last paragraph)

import Definitions.Def_CertDRO_Conc_model

namespace CertDRO.Conc

/-- §B.7, p. 44, the bounds on the transported cost: for `θ ∈ Θ` and `z ∈ Z`,
`0 ≤ c(T(θ; z), z) ≤ K`, where `K = 2 Lc Mz` under case (i) and `K = Mℓ / γ` under case (ii) on `Θ`.
Here `Z ⊆ {‖z‖ ≤ Mz}`, Assumption A holds and `γ > Lzz ≥ 0`. -/
theorem cost_bound {d m : ℕ} (Z : Set (CertDRO.SGD.Data m)) (Θ : Set (CertDRO.SGD.Param d))
    (ℓ : CertDRO.SGD.Param d → CertDRO.SGD.Data m → ℝ) (gθ : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Param d)
    (gz : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Data m) (c : CertDRO.SGD.Data m → CertDRO.SGD.Data m → ℝ) (T : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Data m)
    (Lθθ Lzz Lθz Lzθ γ Lc Mℓ Mz K : ℝ)
    (hZbdd : ∀ z ∈ Z, ‖z‖ ≤ Mz)
    (hA : CertDRO.SGD.AssumptionA Z c) (hB : AssumptionB Θ Z ℓ gθ gz Lθθ Lzz Lθz Lzθ)
    (hγ : Lzz < γ) (hT : IsTransportMap Θ Z ℓ c γ T)
    (hcase : (CaseI Z c Lc ∧ K = 2 * Lc * Mz) ∨ (CaseII Θ Z ℓ γ Lc Mℓ ∧ K = Mℓ / γ)) :
    ∀ θ ∈ Θ, ∀ z ∈ Z, 0 ≤ c (T θ z) z ∧ c (T θ z) z ≤ K := by sorry

end CertDRO.Conc
