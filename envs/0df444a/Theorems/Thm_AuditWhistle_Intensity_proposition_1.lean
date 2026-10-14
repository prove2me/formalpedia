-- Prove2me | Theorems.Thm_AuditWhistle_Intensity_proposition_1
-- name    : AuditWhistle.Intensity.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:27.733856+00:00
-- url     : https://prove2.me/theorems/a043ec29-54c5-4c45-b792-8549b2e07f8f
-- title:
--   Proposition 1, p. 13 — existence and uniqueness of the equilibrium {a*, e₁*, e₀*}, characterized by (7)–(9)
-- statement:
--   Fix a model (parameters $p,\beta,R,\gamma,D,k$ with $0<p<1$, $\tfrac12<\beta<1$, positive $R,\gamma,D,k$, $R/\gamma<1/(1-p)$, $D/k<1/(1-p)$) and an intensity $\tau\in(0,1)$. Then:
--
--   1. there is exactly one equilibrium triple $(a^*,e_1^*,e_0^*)$;
--   2. a triple $(a,e_1,e_0)$ is an equilibrium if and only if $a\in(0,1)$ and
--   $$a=\frac{(1-p)D}{k}\,[\beta\tau e_1+(1-\beta\tau)e_0],\tag{7}$$
--   $$e_1=\min\Big\{1,\ \frac{R}{\gamma}\,\frac{(1-p)(1-a)\beta}{(1-p)(1-a)\beta+p(1-\beta)}\Big\},\tag{8}$$
--   $$e_0=\frac{R}{\gamma}\,\frac{(1-p)(1-a)(1-\beta\tau)}{(1-p)(1-a)(1-\beta\tau)+p\,[1-(1-\beta)\tau]}.\tag{9}$$
--
--   The equilibrium is the object whose dependence on $\tau$ Proposition 2 studies.
--
--   **Formalization Note** The investors' decisions (Lemma 1) are not part of the formalized equilibrium; only the triple $(a^*,e_1^*,e_0^*)$ is. The paper prints no proof of Proposition 1.
-- source:
--   Nan, Tang & Ye, Auditing with a Chance of Whistleblowing, author manuscript dated December 30, 2024 (Management Science, DOI 10.1287/mnsc.2024.04808), p. 13, Proposition 1, (7)–(9)

import Mathlib
import Definitions.Def_AuditWhistle_Intensity_Setting

namespace AuditWhistle.Intensity

theorem proposition_1 (M : Model) (τ : ℝ) (hτ : τ ∈ Set.Ioo (0:ℝ) 1) :
    (∃! x : ℝ × ℝ × ℝ, IsEquilibrium M τ x.1 x.2.1 x.2.2) ∧
    ∀ a e1 e0 : ℝ, IsEquilibrium M τ a e1 e0 ↔
      (a ∈ Set.Ioo (0:ℝ) 1 ∧
        a = (1 - M.p) * M.D / M.k * (M.β * τ * e1 + (1 - M.β * τ) * e0) ∧
        e1 = min 1 (M.R / M.γ * ((1 - M.p) * (1 - a) * M.β /
          ((1 - M.p) * (1 - a) * M.β + M.p * (1 - M.β)))) ∧
        e0 = M.R / M.γ * ((1 - M.p) * (1 - a) * (1 - M.β * τ) /
          ((1 - M.p) * (1 - a) * (1 - M.β * τ) + M.p * (1 - (1 - M.β) * τ)))) := by sorry

end AuditWhistle.Intensity
