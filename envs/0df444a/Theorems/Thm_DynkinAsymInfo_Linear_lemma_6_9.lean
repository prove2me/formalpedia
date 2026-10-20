-- Prove2me | Theorems.Thm_DynkinAsymInfo_Linear_lemma_6_9
-- name    : DynkinAsymInfo.Linear.lemma_6_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:28.380364+00:00
-- url     : https://prove2.me/theorems/892d0ec2-7c53-4708-baaa-37fe3a1d5d2c
-- title:
--   Lemma 6.9 — the ratio A/B is uniquely determined
-- statement:
--   With $\mu_0<0<\mu_1$, $\sigma>0$, and $\varepsilon>0$, the indicial roots in (89) satisfy $0<\beta_1<1$ and $\beta_2<0$. There exists exactly one $z\in(0,1)$ for which
--   $$(1-\beta_2)z^{\beta_1-1}+(\beta_1-1)z^{\beta_2-1}=\frac{\beta_1-\beta_2}{1+\varepsilon}.$$
--   This root is the ratio $A/B$ of the two equilibrium thresholds. The uniqueness makes the subsequent closed-form definitions unambiguous.
-- source:
--   De Angelis, Ekström, Glover, Dynkin Games with Incomplete and Asymmetric Information, arXiv:1810.07674v5, p. 23, Lemma 6.9, (89)–(90)

import Mathlib
import Definitions.Def_DynkinAsymInfo_Linear_ClosedForms

namespace DynkinAsymInfo.Linear
set_option autoImplicit false

/-- De Angelis, Ekström, Glover, arXiv:1810.07674v5, p. 23, Lemma 6.9.
The ratio `A/B` has a unique value in (0,1) satisfying (90). The two root-location
inequalities stated before (89) are included. -/
theorem lemma_6_9 (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1)
    (eps : ℝ) (heps : 0 < eps) :
    beta1 p ∈ Set.Ioo 0 1 ∧ beta2 p < 0 ∧
      ∃! z : ℝ, z ∈ Set.Ioo 0 1 ∧ rootEq p eps z = 0 := by sorry

end DynkinAsymInfo.Linear
