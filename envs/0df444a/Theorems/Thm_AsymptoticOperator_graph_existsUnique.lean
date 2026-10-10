-- Prove2me | Theorems.Thm_AsymptoticOperator_graph_existsUnique
-- name    : AsymptoticOperator.graph_existsUnique
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T14:31:34.610239+00:00
-- url     : https://prove2.me/theorems/2797ec85-9017-407a-b780-c5e3a0b8ff65
-- title:
--   The asymptotic operator $-J_0\partial_t - S$ is a well-defined linear operator on $L^2(S^1,\mathbb{R}^{2n})$
-- statement:
--   Let $S:S^1\to\mathbb{R}^{2n\times2n}$ be continuous. There is exactly one partially defined linear map $A$ on $L^2(S^1,\mathbb{R}^{2n})$ whose graph is the set of pairs $(f,g)$ with $f\in W^{1,2}$ and
--   $$\hat g_k=-2\pi ik\,J_0\hat f_k-(Sf)^\wedge_k\quad\text{for all }k\in\mathbb{Z}.$$
--
--   So $A_S=-J_0\partial_t-S$ is a well-defined unbounded operator, and `asymptoticOperator S` is this map.
-- source:
--   Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, §3.2, equation (3.4); Hofer-Wysocki-Zehnder, Properties of pseudoholomorphic curves in symplectisations II, GAFA 5 (1995) 270-328, https://doi.org/10.1007/BF01895669, Section 3, p. 285, equation (35) (n = 1)

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open ConleyZehnder

/-- Wendl §3.2, (3.4): `A_S = -J₀ ∂ₜ - S` is a well-defined linear operator on
`L²(S¹, ℝ²ⁿ)`: exactly one partially defined linear map has graph `graphSet S`. -/
theorem graph_existsUnique {n : ℕ} (S : C(UnitAddCircle, Mat n)) :
    ∃! A : L2 n →ₗ.[ℝ] L2 n, (A.graph : Set (L2 n × L2 n)) = graphSet S := by sorry

end AsymptoticOperator
