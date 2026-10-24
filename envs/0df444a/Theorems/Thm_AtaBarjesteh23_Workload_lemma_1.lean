-- Prove2me | Theorems.Thm_AtaBarjesteh23_Workload_lemma_1
-- name    : AtaBarjesteh23.Workload.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:32.737323+00:00
-- url     : https://prove2.me/theorems/c6742c7e-c1a2-4c01-a793-f170fa36095f
-- title:
--   Lemma 1, p. 15 — c(x) = x²/(m′H⁻¹m), uniquely attained at ζ⋆(x) = H⁻¹m x/(m′H⁻¹m)
-- statement:
--   Assume the standing assumptions; in particular $H$ is symmetric positive definite and $m\ne0$, so $a=m'H^{-1}m>0$. For every $x\in\mathbb R$, the quadratic program
--   $$c(x)=\min\{\zeta'H\zeta:\ m'\zeta=x,\ \zeta\in\mathbb R^K\}$$
--   has the value and the unique minimizer
--   $$c(x)=\frac{x^2}{m'H^{-1}m},\qquad \zeta^\star(x)=\frac{H^{-1}m}{m'H^{-1}m}\,x.$$
--   Precisely: $x^2/a$ is the least element of $\{\zeta'H\zeta: m'\zeta=x\}$, the vector $\zeta^\star(x)$ is feasible and attains it, and every feasible $\zeta$ attaining it equals $\zeta^\star(x)$.
--
--   The closed form of $c$ turns every later cost expression into an explicit quadratic in the effective drift rate.
--
--   **Formalization Note** $c$ is defined as an infimum; the theorem asserts attainment (`IsLeast`) as well as the value.
-- source:
--   Ata and Barjesteh, An Approximate Analysis of Dynamic Pricing, Outsourcing, and Scheduling Policies for a Multiclass Make-to-Stock Queue in the Heavy Traffic Regime, accepted manuscript (SSRN 3464763; published in Operations Research 71(1):341–357, 2023, doi:10.1287/opre.2022.2361), p. 15, Lemma 1

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting

open Matrix Set

namespace AtaBarjesteh23.Workload

theorem lemma_1 (M : Model) (hM : M.Standing) (x : ℝ) :
    IsLeast {q : ℝ | ∃ ζ : Fin M.K → ℝ, M.m ⬝ᵥ ζ = x ∧ q = ζ ⬝ᵥ (M.H *ᵥ ζ)} (x ^ 2 / M.a) ∧
    M.m ⬝ᵥ ((x / M.a) • (M.H⁻¹ *ᵥ M.m)) = x ∧
    (x / M.a) • (M.H⁻¹ *ᵥ M.m) ⬝ᵥ (M.H *ᵥ ((x / M.a) • (M.H⁻¹ *ᵥ M.m))) = x ^ 2 / M.a ∧
    (∀ ζ : Fin M.K → ℝ, M.m ⬝ᵥ ζ = x → ζ ⬝ᵥ (M.H *ᵥ ζ) = x ^ 2 / M.a →
      ζ = (x / M.a) • (M.H⁻¹ *ᵥ M.m)) ∧
    M.cost x = x ^ 2 / M.a := by sorry

end AtaBarjesteh23.Workload
