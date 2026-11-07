-- Prove2me | Theorems.Thm_DynSort_eq_1
-- name    : DynSort.eq_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:33:51.661653+00:00
-- url     : https://prove2.me/theorems/ba04ab2d-8479-4e8c-9a19-5065f69d20ec
-- title:
--   Equation (1) — $\mathrm{cost}(S)=\int_{\mathbb R}\mathrm{cross}_z(S)\,dz$
-- statement:
--   For every finite sequence $S$ of reals, the function $z\mapsto\mathrm{cross}_z(S)$ is Lebesgue integrable on $\mathbb R$ and
--   $$\mathrm{cost}(S)=\int_{\mathbb R}\mathrm{cross}_z(S)\,dz .$$
--
--   Each adjacent pair crosses exactly the thresholds between its two values, so the identity turns crossing bounds into cost bounds; it is used in Lemma 5, Lemma 8 and Claim 22.
--
--   **Formalization Note** The integral is a Bochner integral, which is $0$ for a non-integrable function; integrability is part of the conclusion.
--
--   Differences from the source:
--   - encoding: ∫_ℝ cross_z(S) dz → integrability of z ↦ cross_z(S) together with the Bochner integral; reason: a Bochner integral of a non-integrable function is 0; the integrand is a bounded step function with compact support, so this is the source's integral
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), §2, p.6 (PDF p.8), eq. (1)

import Mathlib
import Definitions.Def_DynSort_cost
import Definitions.Def_DynSort_cross

namespace DynSort

/-- **Equation (1)**, Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §2, p.6 (PDF p.8): "Since each adjacent pair crosses precisely the
thresholds between its two values, summing over all pairs gives cost(S) = ∫_ℝ cross_z(S) dz."

**Formalization Note.** For every finite sequence `S`, including the empty one and singletons,
the integrand `z ↦ cross_z(S)` is Lebesgue integrable on `ℝ` and its integral is `cost S`. The
integrability clause is stated because a Bochner integral of a non-integrable function is `0`. -/
theorem eq_1 (S : List ℝ) :
    MeasureTheory.Integrable (fun z : ℝ => (cross z S : ℝ)) ∧
      cost S = ∫ z : ℝ, (cross z S : ℝ) := by sorry

end DynSort
