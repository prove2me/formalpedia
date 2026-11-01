-- Prove2me | Theorems.Thm_CascadeCC_eq_17_rate_expansion
-- name    : CascadeCC.eq_17_rate_expansion
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:34:33.370637+00:00
-- url     : https://prove2.me/theorems/8f2a3106-ee23-4764-a510-c2d73a84a007
-- title:
--   Eq. (17) = (EC.37)–(EC.38) — the expansion of the corrected rate
-- statement:
--   Let $v,\sigma,a,\delta^v,\delta^\sigma$ be reals with $\sigma\ne0$, $\sigma+\delta^\sigma\ne0$, and $v=\sigma a$. Then
--
--   $$
--   \frac{v-\delta^v}{\sigma+\delta^\sigma}=a-\frac{\delta^v}{\sigma}-\frac{(v-\delta^v)\delta^\sigma}{\sigma(\sigma+\delta^\sigma)}
--   =a-\frac{\delta^v}{\sigma}-\frac{v\delta^\sigma}{\sigma^2}+\frac{\delta^v\delta^\sigma}{\sigma^2}+\frac{(v-\delta^v)(\delta^\sigma)^2}{\sigma^2(\sigma+\delta^\sigma)}.
--   $$
--
--   This separates the applied correction into its linear part and its quadratic and cubic parts, on which the loss analysis works.
--
--   Differences from the source:
--   - generalization: the identity at the policy's corrected rates, assuming v̂_t feasible → an identity for all reals with nonzero denominators and v = σa; reason: the policy's rates are the case v = v^D_j, σ = σ^D_j, δ^σ = δ^σ_tj
-- source:
--   Najafi, Duenyas, Jasin, Uichanco, Multi-product Dynamic Pricing with Limited Inventories under a Cascade Click Model, SSRN abstract_id=3362921, (17), p.25; (EC.37)–(EC.38), p.ec12

import Mathlib
import Definitions.Def_CascadeCC_Analysis

namespace CascadeCC

variable {J : ℕ}

/-- Equation (17), p.25 = (EC.37)–(EC.38), p.ec12 (SSRN abstract_id=3362921): the expansion of the
corrected rate (v − δv)/(σ + δσ) around a = v/σ, for reals with σ ≠ 0 and σ + δσ ≠ 0. -/
theorem eq_17_rate_expansion (v σ a δv δσ : ℝ) (hσ : σ ≠ 0) (hσ' : σ + δσ ≠ 0) (hv : v = σ * a) :
    (v - δv) / (σ + δσ) = a + (-(δv / σ) - (v - δv) * δσ / (σ * (σ + δσ))) ∧
      (v - δv) / (σ + δσ) =
        a - δv / σ - v * δσ / σ ^ 2 + δv * δσ / σ ^ 2 +
          (v - δv) * δσ ^ 2 / (σ ^ 2 * (σ + δσ)) := by sorry

end CascadeCC
