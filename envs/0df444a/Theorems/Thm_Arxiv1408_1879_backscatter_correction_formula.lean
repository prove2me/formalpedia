-- Prove2me | Theorems.Thm_Arxiv1408_1879_backscatter_correction_formula
-- name    : Arxiv1408_1879.backscatter_correction_formula
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T12:13:12.52322+00:00
-- url     : https://prove2.me/theorems/ad1370a2-1de0-4fb5-9f8b-d7327166002f
-- title:
--   Eq. (25): the backscatter correction C by Abel inversion (as proved)
-- statement:
--   Let $k>0$, let $\tilde\psi:\mathbb{R}\to\mathbb{C}$ be a surface source, and suppose that for every $y\ge0$ the improper integral
--   $$R_0\tilde\psi(y)=\alpha\int_y^\infty\frac{e^{2ik(r-y)}}{\sqrt{r-y}}\,\tilde\psi(r)\,dr$$
--   converges. Let $C$ be continuous on $[0,\infty)$ with $L_0C=R_0\tilde\psi$ on $[0,\infty)$, i.e. $C=L_0^{-1}R_0\tilde\psi$ as in eq. (21). Then for every $x>0$,
--   $$C(x)=\frac1\pi\,\frac{d}{dx}\left[\int_0^x\frac1{\sqrt{x-y}}\int_y^\infty\frac{e^{2ik(r-y)}}{\sqrt{r-y}}\,\tilde\psi(r)\,dr\,dy\right].$$
--   This is the explicit form (25) of the backscatter correction, obtained by solving Abel's integral equation $L_0C=R_0\tilde\psi$.
--
--   **Formalization Note** Eq. (25) is printed with the prefactor $1/(\alpha^2\pi)$, the inner kernel $1/\sqrt{y-r}$ (the square root of a negative number for $r>y$), and the phase $\exp(ikr)$. Abel's solution $L_0^{-1}g=\frac1{\alpha\pi}\frac d{dx}\int_0^x g(y)(x-y)^{-1/2}dy$, applied to $g=R_0\tilde\psi$ with $R_0$ the flat form of $R$ from eq. (6), gives the prefactor $1/\pi$, the kernel $1/\sqrt{r-y}$ and the phase $e^{2ik(r-y)}$. The statement gives this derived formula (as proved). Eq. (20) as printed omits the phase from $R_0$. The statement leaves $\tilde\psi$ general and does not use the first-order form (22) from ref. [12].
-- source:
--   M. Spivack and O. Rath Spivack, Rough surface backscatter and statistics via extended parabolic integral equation, arXiv:1408.1879v2 (2015), claim c009; Section 4.1, eqs. (20), (21), the unnumbered Abel display and eq. (25), PDF pp. 8-9

import Mathlib
import Definitions.Def_Arxiv1408_1879_Basic

open MeasureTheory Filter Topology

namespace Arxiv1408_1879

theorem backscatter_correction_formula (k : ℝ) (hk : 0 < k) (ψt C : ℝ → ℂ)
    (hC : ContinuousOn C (Set.Ici 0))
    (hR : ∀ y : ℝ, 0 ≤ y → ImproperIntegrable (fun r => greenTwoWay k y 0 r 0 * ψt r) y)
    (hLC : ∀ y : ℝ, 0 ≤ y → leftOpFlat k C y = rightOpFlat k ψt y) :
    ∀ x : ℝ, 0 < x → C x = (1 / (Real.pi : ℂ)) * deriv (fun s : ℝ => ∫ y in (0 : ℝ)..s,
      ((1 / Real.sqrt (s - y) : ℝ) : ℂ) *
        improperIntegral (fun r => ((1 / Real.sqrt (r - y) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((2 * k * (r - y) : ℝ) : ℂ)) * ψt r) y) x := by sorry

end Arxiv1408_1879
