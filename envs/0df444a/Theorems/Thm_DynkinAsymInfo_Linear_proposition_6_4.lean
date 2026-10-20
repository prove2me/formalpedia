-- Prove2me | Theorems.Thm_DynkinAsymInfo_Linear_proposition_6_4
-- name    : DynkinAsymInfo.Linear.proposition_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:32.46898+00:00
-- url     : https://prove2.me/theorems/7c09b31a-bb76-421e-b8f1-472a70e0922d
-- title:
--   Proposition 6.4 — reflection of the likelihood at B
-- statement:
--   Fix $B>0$. Let $\Gamma^B$ be the control determined by the running maximum of the likelihood and set $\Phi^B=\Phi(1-\Gamma^B)$. The recovered regulator $L_t=-B\log((1-\Gamma^B_t)/(1-\Gamma^B_0))$ is continuous, nondecreasing, starts at zero and grows only when $\Phi^B=B$. Moreover $\Phi^B_0=\min(\phi,B)$, $0<\Phi^B_t\le B$, and
--   $$\Phi^B_t=(\phi\wedge B)\frac{\Phi_t}{\phi}e^{-L_t/B},\qquad \Gamma^B_0=\max\{0,1-B/\phi\},\qquad \Gamma^B_t<1.$$
--   This gives the reflected belief process that Player 1 uses in the stopping rule.
--
--   **Formalization Note.** The source's reflected SDE (73) is represented by its solved multiplicative form; the source proves their equivalence. Path claims hold almost surely under the original law, which has the same finite-horizon likelihood-path null sets as the tilted law.
-- source:
--   De Angelis, Ekström, Glover, Dynkin Games with Incomplete and Asymmetric Information, arXiv:1810.07674v5, p. 20, Proposition 6.4, (71)–(75); p. 21, solved form

import Mathlib
import Definitions.Def_DynkinAsymInfo_Linear_ClosedForms

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinAsymInfo.Linear
set_option autoImplicit false

/-- De Angelis, Ekström, Glover, arXiv:1810.07674v5, p. 20,
Proposition 6.4 and (71)–(75), in the explicit GBM representation. The reflected
likelihood `Φ^B` equals the Skorokhod solution. The solved multiplicative form of
(73) is stated; the regulator grows only where the reflected process is at B.
The a.s. quantifier uses the original P; the source's tilted law has the same
likelihood-path null sets on each finite horizon. -/
theorem proposition_6_4 {Ω : Type*} [MeasurableSpace Ω] (p : Params)
    (st : Setting Ω) (h62 : p.mu0 < 0 ∧ 0 < p.mu1)
    (x pi B : ℝ) (hx : 0 < x) (hpi : pi ∈ Set.Ioo 0 1)
    (hB : 0 < B) :
    let phi := pi / (1 - pi)
    InA st (FX p st x pi) (GammaB p st x pi B) ∧
    (∀ᵐ a ∂st.P,
      Continuous (fun t => regulatorB p st x pi B t a) ∧
      Monotone (fun t => regulatorB p st x pi B t a) ∧
      regulatorB p st x pi B 0 a = 0 ∧
      PhiB p st x pi B 0 a = min phi B ∧
      (∀ t, 0 < PhiB p st x pi B t a ∧ PhiB p st x pi B t a ≤ B) ∧
      (∀ s t, s ≤ t →
        (∀ u ∈ Set.Icc s t, PhiB p st x pi B u a < B) →
        regulatorB p st x pi B s a = regulatorB p st x pi B t a) ∧
      (∀ t, PhiB p st x pi B t a =
        min phi B * (Phi p st x pi t a / phi) *
          Real.exp (-regulatorB p st x pi B t a / B)) ∧
      GammaB p st x pi B 0 a = max 0 (1 - B / phi) ∧
      (∀ t, GammaB p st x pi B t a < 1)) := by sorry

end DynkinAsymInfo.Linear
