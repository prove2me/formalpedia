-- Prove2me | Theorems.Thm_CostSharingPNE_Potential_gwmc_eq_basis_sum
-- name    : CostSharingPNE.Potential.gwmc_eq_basis_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:29:02.570069+00:00
-- url     : https://prove2.me/theorems/9acc1c2e-8291-40f9-988a-83ac4b561abd
-- title:
--   Theorem 3 proof step (b), pp. 58–59 — GWMC equals its basis expansion
-- statement:
--   Let $W:2^N\to\mathbb R$ and let $\omega$ be a weight system. Write $q_T^W$ for the Möbius coefficient of $W$ at coalition $T$, and $f^T_{\mathrm{GWMC}}[\omega]$ for the basis rule in Table 2. For every coalition $S$ and player $i\in S$, Table 1's generalized weighted marginal contribution rule satisfies
--
--   $$f^W_{\mathrm{GWMC}}[\omega](i,S)=\sum_{\varnothing\ne T\subseteq S}q_T^W f^T_{\mathrm{GWMC}}[\omega](i,S).$$
--
--   This equality connects the closed marginal-contribution formula with the coalition basis used in the proof of Theorem 3.
--
--   **Formalization Note** The sum includes all nonempty subcoalitions of $S$; terms with zero coefficient vanish. The value of $W(\varnothing)$ is arbitrary and cancels in the marginal difference.
-- source:
--   Gopalakrishnan, Marden, Wierman, arXiv:1402.3610v1, Table 1 p. 5; Table 2 (9) p. 8; Theorem 3 proof step (b), pp. 58–59

import Mathlib
import Definitions.Def_CostSharingPNE_Potential_Setting

namespace CostSharingPNE.Potential

/-- Appendix C, Theorem 3 proof step (b): Tables 1 and 2 give the same GWMC rule. -/
theorem gwmc_eq_basis_sum {n : ℕ} (ω : CostSharingPNE.Char.WeightSystem n) (W : CostSharingPNE.Char.Welfare n) :
    ∀ S : Finset (Fin n), ∀ i ∈ S,
      CostSharingPNE.Char.gwmc ω W i S =
        ∑ T ∈ S.powerset.filter Finset.Nonempty,
          CostSharingPNE.Char.mobius W T * gwmcBasis ω T i S := by sorry

end CostSharingPNE.Potential
