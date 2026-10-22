-- Prove2me | Theorems.Thm_FermiCap_Gaussian_lemma_2
-- name    : FermiCap.Gaussian.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:43:13.025583+00:00
-- url     : https://prove2.me/theorems/12ac4ec5-a8c8-4f4a-a116-9e9e63490e92
-- title:
--   Lemma 2 — preservation of Gaussian states
-- statement:
--   For every fermionic product channel $\Phi_b$ with $b_p\in[0,1]$ and every Gaussian input state $\rho$ in Definition 1's sense,
--   $$\Phi_b(\rho)\text{ is Gaussian.}$$
--   This result permits the Gaussian capacity to be described through Gaussian inputs while its ensembles consist of channel outputs.
-- source:
--   Bravyi, Classical capacity of fermionic product channels, arXiv:quant-ph/0507282v1, p. 5, Lemma 2; proof on p. 6

import Mathlib
import Definitions.Def_FermiCap_Gaussian_Capacity

noncomputable section

namespace FermiCap.Gaussian

/-- Lemma 2: fermionic product channels preserve Gaussian states. -/
theorem lemma_2 (n : ℕ) (b : Fin (2 * n) → ℝ) (ρ : Op n)
    (hb : ∀ p, 0 ≤ b p ∧ b p ≤ 1) (hρ : IsGaussian ρ) :
    IsGaussian (channel n b ρ) := by sorry

end FermiCap.Gaussian
