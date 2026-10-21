-- Prove2me | Theorems.Thm_CrowdContest_Pooling_lemma_1
-- name    : CrowdContest.Pooling.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:26.759221+00:00
-- url     : https://prove2.me/theorems/0a775684-d4d9-4c43-9d55-ead11075f1ad
-- title:
--   Lemma 1, p. 15 — an interior symmetric equilibrium effort of a sub-contest satisfies C′(e*) = A^l h(ξ;n)
-- statement:
--   Let $n\ge 2$, let the random factors have a symmetric log-concave density $\psi$, let $B$ be the prize of a sub-contest and $C$ a cost function ($C$ continuous on $[0,\infty)$, $C'>0$, $C''>0$ on $(0,\infty)$). If $s>0$ is a symmetric equilibrium effort of the sub-contest — no effort $e\ge 0$ earns a higher expected payoff $B\,W_\psi(e-s)-C(e)$ against $s$ than $s$ does — then
--   $$C'(s)=B\,h(\xi;n),$$
--   and $s$ is the only positive effort with this property, i.e. $s=C'^{-1}(B\,h(\xi;n))$.
--
--   This is the equilibrium characterization of the separate contest: with $B=A^l$ it gives $e^{l*}(n)=C^{l\prime-1}(A^lh(\xi^l;n))$.
--
--   **Formalization Note** The page's inverse $C'^{-1}$ is replaced by the equivalent inverse-free statement ($C'$ is strictly increasing on $(0,\infty)$). The equilibrium is assumed interior ($s>0$), the restriction of the paper's footnote 8. The lemma is a necessary condition: existence of an equilibrium is not asserted.
-- source:
--   Hu & Wang, Joint vs. Separate Crowdsourcing Contests, authors' accepted manuscript (TSpace; SSRN 2892683; Manag. Sci. doi:10.1287/mnsc.2020.3683), Lemma 1 and footnote 8, p. 15; proof OA p. 1

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_CrowdContest_Pooling_Density
import Definitions.Def_CrowdContest_Pooling_Setting

open MeasureTheory

namespace CrowdContest.Pooling

/-- Lemma 1, p. 15: an interior symmetric equilibrium effort `s > 0` of a sub-contest with prize
`B` and cost `C` satisfies `C'(s) = B h(ξ; n)`, i.e. `s = C'⁻¹(B h(ξ; n))`; and `s` is the only
positive effort with this property. -/
theorem lemma_1 (n : ℕ) (hn : 2 ≤ n) (ψ : ℝ → ℝ) (hψ : IsSymLogConcaveDensity ψ)
    (B : ℝ) (C : ℝ → ℝ) (hC : IsCost C) (s : ℝ) (hs : IsSymEqSub ψ n B C s) (hs0 : 0 < s) :
    deriv C s = B * hFun ψ n ∧
      ∀ e, 0 < e → deriv C e = B * hFun ψ n → e = s := by sorry

end CrowdContest.Pooling
