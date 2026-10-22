-- Prove2me | Theorems.Thm_FermiCap_Gaussian_optimal_ensemble
-- name    : FermiCap.Gaussian.optimal_ensemble
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:42:48.916549+00:00
-- url     : https://prove2.me/theorems/499aaa83-bb02-4912-b8c4-de52b7ee378a
-- title:
--   Section IV.B — an optimal Gaussian signaling ensemble
-- statement:
--   Let $n\ge1$ and let the attenuations be sorted, $1\ge b_1\ge b_2\ge\cdots\ge b_{2n}\ge0$, as assumed throughout Section IV (p. 6). Independently choosing the signs in
--   $$2^{-n}(I\pm c_1)(I\pm i c_2c_3)\cdots(I\pm i c_{2n-2}c_{2n-1})$$
--   gives $2^n$ Gaussian pure states. They are mutually orthogonal and, with uniform weights, each has output entropy $S_{\min,g}(\Phi_b)$; their output ensemble attains the Gaussian capacity. Consequently,
--   $$C_1^g(\Phi_b)=n-S_{\min,g}(\Phi_b).$$
--   This bridges the minimum output entropy of Gaussian inputs and the capacity optimized over their finite output ensembles.
--
--   The sorting assumption is essential for the explicit family: the pairing $c_1$, $c_2c_3$, … is matched to the largest coefficient and then to consecutive pairs. For unsorted $b$ (e.g. $n=1$, $b=(0,1)$) the state $\tfrac12(I+c_1)$ is sent to $I/2$ with entropy $1$, while the Gaussian input $\tfrac12(I+c_2)$ gives a pure output.
-- source:
--   Bravyi, Classical capacity of fermionic product channels, arXiv:quant-ph/0507282v1, p. 6, §IV standing sorted-coefficient convention; p. 8, §IV.B, paragraph beginning ‘It is obvious that’

import Mathlib
import Definitions.Def_FermiCap_Gaussian_Capacity

noncomputable section

namespace FermiCap.Gaussian
open ShadowTomography.QuantumLB (vnEntropy)

/-- The optimal Gaussian signaling ensemble, §IV.B, p. 8, under §IV's standing
assumption (p. 6) that the attenuations are sorted, b₁ ≥ b₂ ≥ ⋯ ≥ b₂ₙ. -/
theorem optimal_ensemble (n : ℕ) (b : Fin (2 * n) → ℝ)
    (hn : 1 ≤ n) (hb : ∀ p, 0 ≤ b p ∧ b p ≤ 1) (hsort : Antitone b) :
    gaussCap n (channel n b) = (n : ℝ) - minOutGaussian n (channel n b) ∧
      ∃ e : Fin (2 ^ n) ≃ (Fin n → Bool),
        let p : Fin (2 ^ n) → ℝ := fun _ => ((2 : ℝ) ^ n)⁻¹
        let σ : Fin (2 ^ n) → Op n := fun a => optimalInput n hn (e a)
        IsProb p ∧
        (∀ a, IsGaussian (σ a) ∧ IsPure (σ a) ∧
          IsDensity (channel n b (σ a)) ∧
          vnEntropy (channel n b (σ a)) = minOutGaussian n (channel n b)) ∧
        (∀ a c, a ≠ c → (σ a * σ c).trace = 0) ∧
        holevo p (fun a => channel n b (σ a)) =
          (n : ℝ) - minOutGaussian n (channel n b) := by sorry

end FermiCap.Gaussian
