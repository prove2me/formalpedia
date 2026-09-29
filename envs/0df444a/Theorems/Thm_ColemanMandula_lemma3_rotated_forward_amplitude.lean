-- Prove2me | Theorems.Thm_ColemanMandula_lemma3_rotated_forward_amplitude
-- name    : ColemanMandula.lemma3_rotated_forward_amplitude
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-24T04:39:18.237169+00:00
-- url     : https://prove2.me/theorems/4e016579-24f2-4a4b-b66f-d68de3fc3f2a
-- title:
--   Coleman–Mandula Lemma 3: small rotations do not kill the elastic amplitude
-- statement:
--   Let $D$ be scattering data satisfying weak elastic analyticity and the occurrence-of-scattering assumption. Let $p\in H_k$, $q\in H_l$ be a good pair (its energy $s=(p+q)^2$ is neither exceptional nor a normal threshold), and let $X\in\mathfrak{so}(3,1)$ annihilate the total momentum, $X(p+q)=0$, so that $\Lambda_\theta=e^{\theta X}$ is a rotation in the centre-of-mass frame. Then there is $\theta_0>0$ such that for all $\theta\in[0,\theta_0]$ and every non-zero two-particle internal state $v\in\mathbb C^{N_k}\otimes\mathbb C^{N_l}$,
--   $$\big\langle (W_k(\Lambda_\theta,p)\otimes W_l(\Lambda_\theta,q))\,v,\; T(p,q\to\Lambda_\theta p,\Lambda_\theta q)\,v\big\rangle\neq0 ,$$
--   i.e. $\langle p,q;v|\,U(\theta)^\dagger T\,|p,q;v\rangle\ne0$: the elastic amplitude into the rotated state does not vanish for small rotation angles.
-- source:
--   S. Coleman and J. Mandula, All Possible Symmetries of the S Matrix, Phys. Rev. 159 (1967) 1251-1256, https://doi.org/10.1103/PhysRev.159.1251, p. 1255, Lemma 3 (Eq. (16))

import Definitions.Def_ColemanMandula_Scattering

open Matrix
open scoped Kronecker

namespace ColemanMandula

theorem lemma3_rotated_forward_amplitude (D : ScatteringData) (hana : D.ElasticAnalytic)
    (hscat : D.ScatteringOccurs) (k l : D.Shell) (p q : FourVec) (hpq : D.GoodPair k l p q)
    (X : Matrix (Fin 4) (Fin 4) ℝ) (hX : IsLorentzGen X) (hXP : X *ᵥ (p + q) = 0) :
    ∃ θ₀ > 0, ∀ θ ∈ Set.Icc 0 θ₀, ∀ v : Fin (D.mult k) × Fin (D.mult l) → ℂ, v ≠ 0 →
      star ((D.wigner k (lorentzExp X θ) p ⊗ₖ D.wigner l (lorentzExp X θ) q) *ᵥ v) ⬝ᵥ
        (D.T k l k l p q (lorentzExp X θ *ᵥ p) (lorentzExp X θ *ᵥ q) *ᵥ v) ≠ 0 := by
  sorry

end ColemanMandula
