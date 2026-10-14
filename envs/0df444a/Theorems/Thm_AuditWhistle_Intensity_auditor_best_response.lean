-- Prove2me | Theorems.Thm_AuditWhistle_Intensity_auditor_best_response
-- name    : AuditWhistle.Intensity.auditor_best_response
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:28.909606+00:00
-- url     : https://prove2.me/theorems/4ca65b7e-26f1-48c2-87b0-9a041031ddf6
-- title:
--   §3.1, (4)–(6), pp. 12–13 — the auditor's best response a = (D/k)(1 − p)Pr(r_b | B, g)
-- statement:
--   Fix a model with $0<p<1$, positive $D,k$ and $D/k<1/(1-p)$. Call $a\in(0,1)$ a best response of the auditor to the detection probability $P$ if it minimizes $(1-p)(1-a)PD+\tfrac12ka^2$ over $a\in(0,1)$.
--
--   1. For every $P\in(0,1]$, $a$ is a best response to $P$ if and only if
--   $$a=\frac{D}{k}(1-p)\,P.\tag{5}$$
--   2. In particular, for $\tau\in(0,1)$, $e_1\in[0,1]$ and $e_0\in(0,1]$, with $P=\Pr(r_b\mid B,g)=\beta\tau e_1+(1-\beta\tau)e_0$ as in (6), $a$ is a best response if and only if $a=\frac{D}{k}(1-p)\,[\beta\tau e_1+(1-\beta\tau)e_0]$.
--
--   This is the auditor's half of the equilibrium of Proposition 1.
--
--   **Formalization Note** The hypothesis $P>0$ is needed: at $P=0$ the infimum of the loss over the open interval $(0,1)$ is not attained. In equilibrium $e_0>0$, so $P>0$ there.
-- source:
--   Nan, Tang & Ye, Auditing with a Chance of Whistleblowing, author manuscript dated December 30, 2024 (Management Science, DOI 10.1287/mnsc.2024.04808), pp. 12–13, §3.1, (4), (5), (6)

import Mathlib
import Definitions.Def_AuditWhistle_Intensity_Setting

namespace AuditWhistle.Intensity

theorem auditor_best_response (M : Model) :
    (∀ P a : ℝ, P ∈ Set.Ioc (0:ℝ) 1 →
      (IsAuditorBR M P a ↔ a = M.D / M.k * (1 - M.p) * P)) ∧
    (∀ τ e1 e0 a : ℝ, τ ∈ Set.Ioo (0:ℝ) 1 → e1 ∈ Set.Icc (0:ℝ) 1 → e0 ∈ Set.Ioc (0:ℝ) 1 →
      (IsAuditorBR M (detectProb M τ e1 e0) a ↔
        a = M.D / M.k * (1 - M.p) * (M.β * τ * e1 + (1 - M.β * τ) * e0))) := by sorry

end AuditWhistle.Intensity
