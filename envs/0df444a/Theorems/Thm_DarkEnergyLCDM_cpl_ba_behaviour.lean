-- Prove2me | Theorems.Thm_DarkEnergyLCDM_cpl_ba_behaviour
-- name    : DarkEnergyLCDM.cpl_ba_behaviour
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T01:09:34.944439+00:00
-- url     : https://prove2.me/theorems/116ce347-fd73-49a5-ba6a-6e76902a52e5
-- title:
--   CPL diverges as $a\to\infty$ for $w_a>0$; BA stays bounded
-- statement:
--   Let $w_0, w_a\in\mathbb R$.
--
--   1. If $w_a>0$, the CPL equation of state $w(a) = w_0 + (1-a)w_a$ (Eq. 19) tends to $-\infty$ as $a\to\infty$.
--   2. The BA equation of state $w(a) = w_0 + w_a\frac{1-a}{a^2+(1-a)^2}$ (Eq. 20) is bounded for all $a>0$: there is $M$ with $|w(a)|\le M$ for every $a>0$.
--
--   This is the comparison after Eq. (20): CPL diverges as the scale factor tends to infinity (for $w_a>0$), whereas BA remains well behaved at all times.
--
--   **Formalization Note** The source describes the CPL divergence as "exponential". The formal statement records only that the CPL equation of state is unbounded (it tends to $-\infty$).
-- source:
--   R. von Marttens, J. Alcaniz, S. Carneiro, "A energia escura e os desafios do modelo cosmológico padrão", Cadernos de Astronomia 7(1), 62–76 (2026), https://doi.org/10.47456/Cad.Astro.v7n1.52249, p. 72, Eqs. (19)–(20) and following text

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs

namespace DarkEnergyLCDM

open Filter

theorem cpl_ba_behaviour (w₀ wₐ : ℝ) :
    (0 < wₐ → Tendsto (fun a => cplEOS w₀ wₐ a) atTop atBot) ∧
    (∃ M : ℝ, ∀ a : ℝ, 0 < a → |baEOS w₀ wₐ a| ≤ M) := by sorry

end DarkEnergyLCDM
