-- Prove2me | Theorems.Thm_BregmanPPA_IneqMult_lemmaA3
-- name    : BregmanPPA.IneqMult.lemmaA3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:20:34.721047+00:00
-- url     : https://prove2.me/theorems/85047694-8247-4ea8-b35d-e2ed4f0ddd39
-- title:
--   Lemma A3 — everywhere finite and differentiable monotone conjugate
-- statement:
--   Let $F$ be closed, proper, and essentially strictly convex, finite on the strictly positive orthant. If the image of its subdifferential contains that orthant, then its monotone conjugate has full domain and is differentiable everywhere:
--
--   $$\operatorname{dom}F^{*+}=\mathbb R^m,\qquad F^{*+}\text{ is differentiable on }\mathbb R^m.$$
--
--   This result is the appendix bridge from general convex analysis to Lemma 3's Bregman-function case.
--
--   **Formalization Note** Essential strict convexity is strict convexity on every convex subset of $\operatorname{dom}\partial F$. Full domain states that every extended-real value is finite before differentiability is asserted of its real form.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), pp. 223–224, Lemma A3, https://doi.org/10.1287/moor.18.1.202

import Mathlib
import Definitions.Def_BregmanPPA_IneqMult_Program

open Filter Topology InertialFB.IFB

namespace BregmanPPA.IneqMult

/-- Lemma A3, pp. 223–224: full domain and differentiability of the monotone conjugate. -/
theorem lemmaA3 {m : ℕ} (F : E m → EReal)
    (hproper : IsProperFn F) (hconvex : IsConvexFn F)
    (hclosed : LowerSemicontinuous F)
    (hstrict : EssentiallyStrictlyConvex F)
    (hfinite : ∀ p : E m, p ∈ posOrthant m → F p ≠ ⊤)
    (him : ∀ z : E m, z ∈ posOrthant m →
      ∃ p : E m, IsSubgradient F p z) :
    (∀ z : E m, monoConjE F z ≠ ⊤ ∧ monoConjE F z ≠ ⊥) ∧
    Differentiable ℝ (fun z : E m => (monoConjE F z).toReal) := by sorry

end BregmanPPA.IneqMult
