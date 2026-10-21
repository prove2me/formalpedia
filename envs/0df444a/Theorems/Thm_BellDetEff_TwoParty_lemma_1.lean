-- Prove2me | Theorems.Thm_BellDetEff_TwoParty_lemma_1
-- name    : BellDetEff.TwoParty.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:56.602566+00:00
-- url     : https://prove2.me/theorems/d7fe4eb6-fc1f-4d5e-8cf0-884da166d1ac
-- title:
--   Lemma 1 — for η1 < η2, if p^NS_η2 is LHV-simulable then so is p^NS_η1
-- statement:
--   Let $p$ be a no-signaling behaviour with finite output alphabets, and let $0\le\eta_1<\eta_2\le 1$. If the behaviour $p_{\eta_2}$ under detector efficiency $\eta_2$ (eq. (2)) can be simulated by a local hidden variable model, then so can $p_{\eta_1}$.
--
--   Local simulability is therefore monotone in the detector efficiency, which is what makes the threshold $e(p)$ and the bound $\eta^*_{NS}$ of eq. (A3) meaningful: the set of efficiencies with a local model is an interval starting at $0$.
--
--   **Formalization Note** The range $0\le\eta_1$, $\eta_2\le 1$ is implicit in the paper (efficiencies are probabilities); outside $[0,1]$ the behaviour of eq. (2) has negative entries. LHV models range over arbitrary probability spaces.
-- source:
--   Cao & Peng, Tight detection efficiency bounds of Bell tests in no-signaling theories, arXiv:1607.04350v1, p. 5, Appendix A, Lemma 1

import Mathlib
import Definitions.Def_BellDetEff_TwoParty_Efficiency

namespace BellDetEff.TwoParty

/-- Lemma 1 (Cao–Peng, arXiv:1607.04350v1, p. 5): for efficiencies `0 ≤ η₁ < η₂ ≤ 1`, if
`p^NS_{η₂}` can be simulated by an LHV model, then so can `p^NS_{η₁}`. -/
theorem lemma_1 {KA KB MA MB : ℕ} (p : Fin KA → Fin KB → Fin MA → Fin MB → ℝ)
    (hp : IsBehaviour p) (hns : NoSignaling p) (η₁ η₂ : ℝ) (h₁ : 0 ≤ η₁) (h₁₂ : η₁ < η₂)
    (h₂ : η₂ ≤ 1) (hsim : LHVSimulable (withEff p η₂)) :
    LHVSimulable (withEff p η₁) := by sorry

end BellDetEff.TwoParty
