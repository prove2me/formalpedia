-- Prove2me | Theorems.Thm_ClassNumberFormula_gaussian_residue_eq_pi_div_four
-- name    : ClassNumberFormula.gaussian_residue_eq_pi_div_four
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T12:53:14.110319+00:00
-- url     : https://prove2.me/theorems/d71fd21a-3a91-4972-9909-da3dc2d3ee69
-- title:
--   $K=\mathbb Q(i)$: the residue of $\zeta_K$ at $s=1$ is $\pi/4$
-- statement:
--   Let $K$ be a quadratic number field containing a square root of $-1$, so that $K\cong\mathbb Q(i)$. Then
--   $$\lim_{s\to1^+}(s-1)\,\zeta_K(s) = \frac{\pi}{4}.$$
--
--   This is the case of the class number formula worked out in the source's proof: here $r_1 = 0$, $r_2 = 1$, $h_K = 1$, $\mathrm{Reg}_K = 1$, $w_K = 4$ and $D_K = -4$.
--
--   **Formalization Note** The limit is taken along real $s\to1^+$, using Mathlib's `dedekindZeta` (the Dirichlet series).
-- source:
--   Wikipedia, "Class number formula" (revision oldid=1366411311), https://en.wikipedia.org/w/index.php?title=Class_number_formula&oldid=1366411311, section "Proof", second paragraph ("concluding that the residue is one quarter of pi")

import Mathlib
open NumberField NumberField.InfinitePlace NumberField.Units Filter Topology Real

namespace ClassNumberFormula

theorem gaussian_residue_eq_pi_div_four (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (hi : ∃ i : K, i ^ 2 = -1) :
    Tendsto (fun s : ℝ => ((s : ℂ) - 1) * dedekindZeta K s) (𝓝[>] 1)
      (𝓝 ((π / 4 : ℝ) : ℂ)) := by sorry

end ClassNumberFormula
