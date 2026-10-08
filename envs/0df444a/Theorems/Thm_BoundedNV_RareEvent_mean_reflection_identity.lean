-- Prove2me | Theorems.Thm_BoundedNV_RareEvent_mean_reflection_identity
-- name    : BoundedNV.RareEvent.mean_reflection_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T20:01:52.883055+00:00
-- url     : https://prove2.me/theorems/e89e0a6f-560a-4e27-ae4d-e8e28b6ad684
-- title:
--   Proof of Proposition 4, p. 587 — reflected logit mean identity (51)–(53)
-- statement:
--   Let $a<b$, $m=(a+b)/2$, and $r=(b-a)/2$. For a continuous utility $u$ on $[a,b]$ and $\beta>0$, let $\psi$ be its logit choice density on that interval. Its mean satisfies
--
--   $$
--   \mathbb E[Y]=m+\int_0^r v\bigl[\psi(m+v)-\psi(m-v)\bigr]\,dv.
--   $$
--
--   This reflection identity converts a comparison of logit densities into a comparison of expected orders with the midpoint.
--
--   **Formalization Note** Continuity on the compact, nonempty decision interval makes the normalizer finite and positive, so the displayed expectation is a genuine one.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, p. 587 (PDF 22), proof of Proposition 4, eqs. (51)–(53)

import Mathlib
import Definitions.Def_BoundedNV_RareEvent_Logit

namespace BoundedNV.RareEvent

/-- Equations (51)–(53) in the proof of Proposition 4, p. 587. -/
theorem mean_reflection_identity (u : ℝ → ℝ) (β a b : ℝ)
    (hβ : 0 < β) (hab : a < b)
    (hu : ContinuousOn u (Set.Icc a b)) :
    BoundedNV.Uniform.logitExp (Set.Icc a b) u β id =
      (a + b) / 2 + ∫ v in (0 : ℝ)..((b - a) / 2),
        v * (BoundedNV.Uniform.logitDensity (Set.Icc a b) u β ((a + b) / 2 + v) -
          BoundedNV.Uniform.logitDensity (Set.Icc a b) u β ((a + b) / 2 - v)) := by sorry

end BoundedNV.RareEvent
