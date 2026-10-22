-- Prove2me | Theorems.Thm_FermiCap_Gaussian_eq_27
-- name    : FermiCap.Gaussian.eq_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:43:03.006979+00:00
-- url     : https://prove2.me/theorems/eb5dff71-ca10-4517-8276-17e586f637f3
-- title:
--   Equation (27) — minimum output entropy on even Gaussian inputs
-- statement:
--   For $n\ge1$, let $b_1\ge\cdots\ge b_{2n}$ with every $b_p\in[0,1]$. The minimum output entropy of $\Phi_b$ over even Gaussian input states is attained and equals
--   $$S_{\min,e}(\Phi_b)=\sum_{j=1}^{n}H\left(\frac{1+b_{2j-1}b_{2j}}{2}\right).$$
--   This is the intermediate entropy formula for the even Gaussian class, before the general Gaussian optimization.
-- source:
--   Bravyi, Classical capacity of fermionic product channels, arXiv:quant-ph/0507282v1, p. 6, §IV standing sorted-coefficient convention; p. 7, eq. (27) and eqs. (32)–(33) for attainment

import Mathlib
import Definitions.Def_FermiCap_Gaussian_Capacity

noncomputable section
open ShadowTomography.QuantumLB (vnEntropy)

namespace FermiCap.Gaussian

/-- Eq. (27), §IV.A: the even-Gaussian minimum and its attainment. -/
theorem eq_27 (n : ℕ) (b : Fin (2 * n) → ℝ)
    (hn : 1 ≤ n) (hb : ∀ p, 0 ≤ b p ∧ b p ≤ 1) (hsort : Antitone b) :
    minOutEvenGaussian n (channel n b) = evenFormula n b ∧
      ∃ ρ : Op n, IsEvenGaussian ρ ∧ IsDensity (channel n b ρ) ∧
        vnEntropy (channel n b ρ) = evenFormula n b := by sorry

end FermiCap.Gaussian
