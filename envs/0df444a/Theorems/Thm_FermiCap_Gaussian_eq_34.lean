-- Prove2me | Theorems.Thm_FermiCap_Gaussian_eq_34
-- name    : FermiCap.Gaussian.eq_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:43:06.844995+00:00
-- url     : https://prove2.me/theorems/513fdebb-096a-422c-84f6-2d6c77c6ca6e
-- title:
--   Equation (34) — minimum output entropy on Gaussian inputs
-- statement:
--   For $n\ge1$, let $b_1\ge\cdots\ge b_{2n}$ with every $b_p\in[0,1]$. The minimum output entropy of $\Phi_b$ over all Gaussian input states is attained and equals
--   $$S_{\min,g}(\Phi_b)=H\left(\frac{1+b_1}{2}\right)+\sum_{j=1}^{n-1}H\left(\frac{1+b_{2j}b_{2j+1}}{2}\right).$$
--   The extra linear Majorana freedom distinguishes this formula from the even-Gaussian one. Attainment is supplied by the state displayed in Eq. (36).
-- source:
--   Bravyi, Classical capacity of fermionic product channels, arXiv:quant-ph/0507282v1, p. 6, §IV standing sorted-coefficient convention; p. 7, eq. (34); p. 8, eq. (36) for attainment

import Mathlib
import Definitions.Def_FermiCap_Gaussian_Capacity

noncomputable section
open ShadowTomography.QuantumLB (vnEntropy)

namespace FermiCap.Gaussian

/-- Eq. (34), §IV.B: the Gaussian minimum and its attainment. -/
theorem eq_34 (n : ℕ) (b : Fin (2 * n) → ℝ)
    (hn : 1 ≤ n) (hb : ∀ p, 0 ≤ b p ∧ b p ≤ 1) (hsort : Antitone b) :
    minOutGaussian n (channel n b) = gaussFormula n hn b ∧
      ∃ ρ : Op n, IsGaussian ρ ∧ IsDensity (channel n b ρ) ∧
        vnEntropy (channel n b ρ) = gaussFormula n hn b := by sorry

end FermiCap.Gaussian
