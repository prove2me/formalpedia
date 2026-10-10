-- Prove2me | Theorems.Thm_ConleyZehnder_argLift_exists_increment_unique
-- name    : ConleyZehnder.argLift_exists_increment_unique
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T16:13:40.84951+00:00
-- url     : https://prove2.me/theorems/9b09b2f2-9620-40ae-aad1-0af8e49c7a5a
-- title:
--   A continuous map $[0,1]\to S^1$ has a continuous argument, with a well-defined increment
-- statement:
--   Let $f:[0,1]\to\mathbb C$ be continuous with $|f(t)|=1$ for all $t$. Then
--
--   1. there is a continuous $\theta:[0,1]\to\mathbb R$ with $f(t)=e^{i\theta(t)}$ for all $t$, and
--   2. any two such continuous arguments $\theta,\theta'$ of $f$ have the same increment: $\theta(1)-\theta(0)=\theta'(1)-\theta'(0)$.
--
--   This makes the degree (winding number) of a loop in $S^1$, and the total change of argument along a path in $S^1$, well defined; it is used for $\hat\rho\circ\psi$ in the definitions of the Conley–Zehnder and Maslov indices.
--
--   Formalization note: "continuous argument" is the predicate `IsArgLift f θ` of the definition module `ConleyZehnder_Setting` (`θ` continuous and `f t = exp(θ t · i)` for all `t`).
-- source:
--   Standard path lifting for the covering $\mathbb R\to S^1$, $s\mapsto e^{is}$; e.g. Hatcher, Algebraic Topology (2002), Proposition 1.30; used in Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Section 2, Definition 7 and Corollary 12

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- A continuous `f : [0, 1] → S¹ ⊆ ℂ` has a continuous argument, and all continuous
arguments of `f` have the same increment `θ(1) - θ(0)`. -/
theorem argLift_exists_increment_unique {f : unitInterval → ℂ} (hf : Continuous f)
    (h1 : ∀ t, ‖f t‖ = 1) :
    (∃ θ, IsArgLift f θ) ∧
      ∀ θ θ', IsArgLift f θ → IsArgLift f θ' → θ 1 - θ 0 = θ' 1 - θ' 0 := by sorry

end ConleyZehnder
