-- Prove2me | Theorems.Thm_ConvexRMDP_Supplement_lemma_5_2
-- name    : ConvexRMDP.Supplement.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:57:54.570776+00:00
-- url     : https://prove2.me/theorems/14fb13c4-e977-4b0e-95ac-908bf0a16d98
-- title:
--   Lemma 5.2 — the identity $\alpha\log x-\frac{\alpha}{\gamma}\log\frac{\alpha}{\gamma}+\frac{\alpha}{\gamma}=\alpha\log\frac{x}{\alpha}+\frac{1-\gamma}{\gamma}\alpha\log\frac1\alpha+\dots$
-- statement:
--   Let $\gamma \in (0,1)$ be the discount factor, $\alpha > 0$ and $x \ge 1$. Then
--
--   $$
--   \alpha\log(x) - \frac{\alpha}{\gamma}\log\Big(\frac{\alpha}{\gamma}\Big) + \frac{\alpha}{\gamma} = \alpha\log\Big(\frac{x}{\alpha}\Big) + \Big(\frac{1-\gamma}{\gamma}\Big)\alpha\log\Big(\frac1\alpha\Big) + \Big(\frac{1+\log(\gamma)}{\gamma}\Big)\alpha .
--   $$
--
--   The identity rewrites the objective of (5.8) through the perspective $(\alpha, x) \mapsto \alpha\log(x/\alpha)$ of the logarithm, which is concave and representable with the exponential cone; this gives (5.9) and then (5.3).
--
--   Differences from the source: none.
-- source:
--   Grand-Clément & Petrik, arXiv:2209.10187v2, Lemma 5.2, p.18; proof in App. D

import Mathlib

namespace ConvexRMDP

namespace Supplement

/-- **Lemma 5.2** (Grand-Clément & Petrik, arXiv:2209.10187v2, p.18; proof in App. D). Let `α > 0`,
`x ≥ 1`. Then
`α log(x) − (α/γ) log(α/γ) + α/γ = α log(x/α) + ((1−γ)/γ) α log(1/α) + ((1+log(γ))/γ) α`.

**Formalization Note.** `γ ∈ (0,1)` is the discount factor (standing assumption of §3.1). -/
theorem lemma_5_2 (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (α x : ℝ) (hα : 0 < α) (hx : 1 ≤ x) :
    α * Real.log x - (α / γ) * Real.log (α / γ) + α / γ =
      α * Real.log (x / α) + ((1 - γ) / γ) * α * Real.log (1 / α) +
        ((1 + Real.log γ) / γ) * α := by sorry

end Supplement

end ConvexRMDP
