-- Prove2me | Theorems.Thm_ConleyZehnder_argLift_increment_eq_of_homotopy
-- name    : ConleyZehnder.argLift_increment_eq_of_homotopy
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T17:04:24.73477+00:00
-- url     : https://prove2.me/theorems/41d11719-06fb-4abb-82ea-d7896b2f532d
-- title:
--   The change of argument along a path in $S^1$ is invariant under homotopies fixing the endpoints
-- statement:
--   Let $H:[0,1]\times[0,1]\to\mathbb C$ be continuous with $|H(s,t)|=1$ for all $(s,t)$, and suppose that $H(s,0)=H(0,0)$ and $H(s,1)=H(0,1)$ for all $s$. Let $\theta,\theta':[0,1]\to\mathbb R$ be continuous with $H(0,t)=e^{i\theta(t)}$ and $H(1,t)=e^{i\theta'(t)}$ for all $t$. Then
--   $$\theta(1)-\theta(0)=\theta'(1)-\theta'(0).$$
--
--   So the total change of argument of a path in $S^1$ depends only on its homotopy class relative to the endpoints. It is used for paths $t\mapsto\hat\rho(\psi(t))$ in the definitions of the Conley–Zehnder and Maslov indices.
--
--   Formalization note: the first coordinate of `H : C(unitInterval × unitInterval, ℂ)` is the homotopy parameter $s$; "continuous argument" is the predicate `IsArgLift` of the definition module `ConleyZehnder_Setting`.
-- source:
--   Standard homotopy invariance of path lifting for the covering $\mathbb R\to S^1$, $s\mapsto e^{is}$; e.g. Hatcher, Algebraic Topology (2002), Proposition 1.30; used in Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Section 2, paragraph before Definition 7, p. 6

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- If `H : [0, 1] × [0, 1] → S¹ ⊆ ℂ` is continuous and `H (s, 0)`, `H (s, 1)` do not depend on
`s`, then continuous arguments of `t ↦ H (0, t)` and of `t ↦ H (1, t)` have the same
increment `θ(1) - θ(0)`. -/
theorem argLift_increment_eq_of_homotopy
    (H : C(unitInterval × unitInterval, ℂ)) (hH : ∀ p, ‖H p‖ = 1)
    (h0 : ∀ s, H (s, 0) = H (0, 0)) (h1 : ∀ s, H (s, 1) = H (0, 1))
    (θ θ' : unitInterval → ℝ) (hθ : IsArgLift (fun t => H (0, t)) θ)
    (hθ' : IsArgLift (fun t => H (1, t)) θ') :
    θ 1 - θ 0 = θ' 1 - θ' 0 := by sorry

end ConleyZehnder
