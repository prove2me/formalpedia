-- Prove2me | Theorems.Thm_FamousTheorems_eventually_eq_zero_or_eventually_ne_zero
-- name    : FamousTheorems.eventually_eq_zero_or_eventually_ne_zero
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:26:06.958475+00:00
-- url     : https://prove2.me/theorems/752824dc-2564-463c-a962-596823fe407d
-- title:
--   The dichotomy for zeros of an analytic function
-- statement:
--   **Zeros of an analytic function are isolated**, in dichotomy form. If $f$ is analytic at a point then either $f$ vanishes identically near that point, or it is nonzero on a punctured neighbourhood: $$f \equiv 0 \text{ near } z_0 \quad\text{or}\quad f(z) \neq 0 \text{ for all } z \neq z_0 \text{ near } z_0.$$ There is no middle ground — an analytic function cannot have a sequence of zeros accumulating at a point without being identically zero nearby. The reason is that a nonzero analytic function has a finite order of vanishing $k$ at $z_0$ and factors as $(z-z_0)^k g(z)$ with $g(z_0) \neq 0$, and continuity of $g$ then isolates the zero. This local dichotomy is what powers the identity theorem, the definition of the order of a zero or pole, the argument principle, and the well-definedness of meromorphic functions. **Formalization note.** Both alternatives are stated with the `eventually` filter at `𝓝[≠] z₀`, so "near" means on some punctured neighbourhood. The result is Mathlib's `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem eventually_eq_zero_or_eventually_ne_zero :
    ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
    {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E} {z₀ : 𝕜}, 
    AnalyticAt 𝕜 f z₀ → (∀ᶠ (z : 𝕜) in 𝓝 z₀, f z = 0) ∨ ∀ᶠ (z : 𝕜) in 𝓝[≠] z₀, f z ≠ 0 := by sorry

end FamousTheorems
