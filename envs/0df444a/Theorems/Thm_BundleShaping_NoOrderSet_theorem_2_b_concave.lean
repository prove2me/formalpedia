-- Prove2me | Theorems.Thm_BundleShaping_NoOrderSet_theorem_2_b_concave
-- name    : BundleShaping.NoOrderSet.theorem_2_b_concave
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:12:16.112799+00:00
-- url     : https://prove2.me/theorems/54af5831-c1ee-4a72-b92b-72b30a00bad6
-- title:
--   Theorem 2(b), concavity, p. 23 — G_t(y, z, q) is jointly concave in (y, z, q)
-- statement:
--   In the bundle-to-stock model under the standing assumptions, for every period $1\le t\le T$ the objective of (9),
--
--   $$G_t(y,z,q)=\lambda_t\pi_t(q)-c^p_t(y-\lambda_tAq)-H_t(y,z,q)+\beta E\,V_{t+1}(y-Ad_t(q,\varepsilon_t)),$$
--
--   is jointly concave in $(y,z,q)$ on $\mathbb R^I\times\mathbb R^J\times\Omega$.
--
--   Joint concavity in all decisions, including the market shares, is what makes the optimal policy a constrained order-up-to policy.
--
--   **Formalization Note.** The domain is $\mathbb R^I\times\mathbb R^J\times\Omega$, since $\tau_t$ is only assumed concave on $\Omega$.
-- source:
--   Song & Xue, Demand Shaping Through Bundling and Product Configuration, SSRN 3168907 (version of Aug. 19, 2020), p. 23, Theorem 2(b), first clause

import Mathlib
import Definitions.Def_BundleShaping_NoOrderSet_Model

namespace BundleShaping.NoOrderSet

open Matrix

variable {I J : Type} [Fintype I] [Fintype J]

theorem theorem_2_b_concave (P : Params I J) (hS : P.Standing) (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) : ConcaveOn ℝ (Set.univ ×ˢ Set.univ ×ˢ P.Ω) (fun v : (I → ℝ) × (J → ℝ) × (J → ℝ) => P.G t v.1 v.2.1 v.2.2) := by sorry

end BundleShaping.NoOrderSet
