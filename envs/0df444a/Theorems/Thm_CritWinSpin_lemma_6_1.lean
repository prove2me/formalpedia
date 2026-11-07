-- Prove2me | Theorems.Thm_CritWinSpin_lemma_6_1
-- name    : CritWinSpin.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:44:49.365848+00:00
-- url     : https://prove2.me/theorems/beb48abe-f8ff-400d-8af3-5fa227a4d810
-- title:
--   Lemma 6.1, p.21 — the reweighting identity (31) and the $\sigma$-marginal $\pi^\rho_{\tilde J,\tilde h}$
-- statement:
--   Let $H(y)=\frac12y^\top J_0y+h_0^\top y$ on $\{\pm1\}^n$ have zero diagonal, $\beta=\tau+\theta$, $\theta>0$, $r\ge1$, and $q(y,\sigma)=\mu_H(y)\nu_y(\sigma)$. For every $(y,\sigma)\in\mathrm{supp}(q)$, $D_y(\sigma)=H(y\odot(1_n+\xi))-H(y)$ and
--   $$q(y,\sigma)e^{D_y(\sigma)}=\frac{2^{-t(\sigma)}}{Z_HZ_+^n}\rho^{\otimes N}(\sigma)e^{\tilde H(\sigma)}.$$
--   With $Z_D=\mathbb E_q[e^{D_y(\sigma)}]$, the $\sigma$-marginal of $q(y,\sigma)e^{D_y(\sigma)}/Z_D$ is $\pi^\rho_{\tilde J,\tilde h}$.
--
--   This is the exact link between the binary source and the lifted spin system.
--
--   Differences from the source:
--   - generalization: û ∈ ℚ_{>0} dyadic with (28) → any real û > 0; reason: (31) uses neither rationality nor (28), and a dyadic û with (28) is a positive real
--   - encoding: H̃(σ) of (29) → the energy ½σᵀJ̃σ + h̃ᵀσ of the lift (30); reason: (29) and (30) define the same function; this is proved in the mission's sanity file
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Lemma 6.1, p.21, eq. (31); §6.1, pp.20–21

import Mathlib
import Definitions.Def_CritWinSpin_nuPm
set_option autoImplicit false

namespace CritWinSpin

/-- **Lemma 6.1** (Liu–Zhang–Ren, STOC 2027 submission, manuscript sha256 f77584da…, p.21). For
`q(y, σ) = μ_H(y) ν_y(σ)` and every `(y, σ) ∈ supp(q)`: `D_y(σ) = H(y ⊙ (1_n + ξ)) − H(y)` and
`q(y, σ) e^{D_y(σ)} = 2^{−t(σ)} / (Z_H Z_+^n) ρ^{⊗N}(σ) e^{H̃(σ)}`, eq. (31). With `Z_D = E_q[e^{D_y(σ)}]`,
the `σ`-marginal of `q e^{D}/Z_D` is `π^ρ_{J̃,h̃}`. -/
theorem lemma_6_1 (S : SpinLaw) (hS : IsGHS S) {n r : ℕ} (hr : 1 ≤ r)
    (J₀ : Matrix (Fin n) (Fin n) ℝ) (h₀ : Fin n → ℝ) (hsym : J₀.IsSymm) (hdiag : ∀ i, J₀ i i = 0)
    (θ û : ℝ) (hθ : 0 < θ) (hû : 0 < û) :
    let β : ℝ := tau S + θ
    let q : BinCfg n → Config S (Fin n × Fin r) → ℝ := fun y σ => muH J₀ h₀ y * nuProd S β y σ
    (∀ (y : BinCfg n) (σ : Config S (Fin n × Fin r)), 0 < q y σ →
      Dy J₀ h₀ û y σ =
          energy J₀ h₀ (fun i => spinOf (y i) * (1 + xi û σ i)) - energy J₀ h₀ (binVec y) ∧
      q y σ * Real.exp (Dy J₀ h₀ û y σ) =
        (1 / (2 : ℝ) ^ tiedCount σ) /
            ((∑ y' : BinCfg n, Real.exp (energy J₀ h₀ (binVec y'))) * zPlus S β r ^ n) *
          prodRho S σ * Real.exp (energy (liftJ r β û J₀) (liftH r û h₀) (spinVal σ))) ∧
    (∀ σ : Config S (Fin n × Fin r),
      (∑ y : BinCfg n, q y σ * Real.exp (Dy J₀ h₀ û y σ)) /
          (∑ y' : BinCfg n, ∑ σ' : Config S (Fin n × Fin r),
            q y' σ' * Real.exp (Dy J₀ h₀ û y' σ')) =
        gibbs S (liftJ r β û J₀) (liftH r û h₀) σ) := by sorry

end CritWinSpin
