-- Prove2me | Theorems.Thm_FirstOrderFG_lemma_B_2
-- name    : FirstOrderFG.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:46:23.044662+00:00
-- url     : https://prove2.me/theorems/4acebfbd-3a26-408d-9323-0107323f077a
-- title:
--   Lemma B.2 — scalar suprema for $D_{\varphi_0}$ and $D_\varphi$
-- statement:
--   Let $\varphi_0(z)=-\ln z$ and $\varphi(z)=z\ln z-\ln(1-z)$. For $p\in(0,1)$, $g\ge0$, $a>0$ and $\theta>0$,
--   $$
--   \sup_{0<y<1}\Big\{(p-y)g-\frac1aD_{\varphi_0}(y,p)\Big\}\le\frac a2p^2g^2, \tag{74}
--   $$
--   and, if moreover $\theta\le1/8$ and $g\le1/(1-p)$,
--   $$
--   \sup_{0<y<1}\Big\{(p-y)g-\frac1\theta D_\varphi(y,p)\Big\}\le\theta\min\{p,(1-p)^2\}g^2. \tag{75}
--   $$
--
--   These coordinatewise bounds control the stability term of the master's mirror-descent step.
--
--   Differences from the source:
--   - encoding: $\sup_{0<y<1}\{\cdots\}\le B$ → for every $y\in(0,1)$, $\cdots\le B$; reason: equivalent; avoids the real supremum
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Lemma B.2, Eqs. (74)–(75), p.26

import Mathlib
import Definitions.Def_FirstOrderFG_Dphi0
import Definitions.Def_FirstOrderFG_Dphi

namespace FirstOrderFG

/-- **Lemma B.2: the scalar suprema for `φ₀` and `φ`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Lemma B.2, p.26: "For
`p ∈ (0, 1)`, `g ≥ 0`, `a > 0` and `θ > 0`,
`sup_{0<y<1} {(p − y)g − (1/a) D_{φ₀}(y, p)} ≤ (a/2) p² g²`, (74)
`sup_{0<y<1} {(p − y)g − (1/θ) D_φ(y, p)} ≤ θ min{p, (1 − p)²} g²`, (75)
where the second inequality assumes `θ ≤ 1/8` and `g ≤ 1/(1 − p)`."

**Formalization Note.** Each supremum bound is stated as the bound for every `y ∈ (0,1)`, which is
equivalent and avoids the real `sSup`. `φ₀(z) = −ln z`, `φ(z) = z ln z − ln(1 − z)`. -/
theorem lemma_B_2 (p g a θ : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hg : 0 ≤ g) (ha : 0 < a)
    (hθ : 0 < θ) :
    (∀ y ∈ Set.Ioo (0 : ℝ) 1, (p - y) * g - 1 / a * Dphi0 y p ≤ a / 2 * p ^ 2 * g ^ 2) ∧
    (θ ≤ 1 / 8 → g ≤ 1 / (1 - p) →
      ∀ y ∈ Set.Ioo (0 : ℝ) 1, (p - y) * g - 1 / θ * Dphi y p ≤ θ * min p ((1 - p) ^ 2) * g ^ 2) := by sorry

end FirstOrderFG
