-- Prove2me | Theorems.Thm_AssortSearch_SearchQC_f_mono_g_anti
-- name    : AssortSearch.SearchQC.f_mono_g_anti
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:32:02.490042+00:00
-- url     : https://prove2.me/theorems/b82bf1d1-e8de-4d68-8f47-4d7cbc478793
-- title:
--   Proof of Theorem 5: $f(v_j)$ is increasing and $g(v_j)$ is decreasing
-- statement:
--   Let $v_i>0$ for all variants, $v_0>0$, $\lambda>0$, $m\in\mathbb R$, $S$ an assortment and $V_S=v_0+\sum_{i\in S}v_i$. Let the cost $c$ be concave on $[0,1]$ and differentiable on $(0,1)$. Then on $v_j\in(0,\infty)$ the function
--   $$f(v_j)=m-c'\Bigl(\frac{\bar H(v_j)v_j}{v_j+V_S}\Bigr)$$
--   is nondecreasing, and the function
--   $$g(v_j)=m\sum_{i\in S}v_i-\sum_{i\in S}c'\Bigl(\frac{\bar H(v_j)v_i}{v_j+V_S}\Bigr)v_i$$
--   is nonincreasing, where $\bar H(v_j)=1-e^{-\lambda(v_j+V_S)}$.
--
--   The paper asserts this "by a similar argument as in Theorem 4" without further detail. It is the monotonicity used in both cases of the proof of Theorem 5.
--
--   **Formalization Note** "Increasing"/"decreasing" are stated in the weak sense (`MonotoneOn`, `AntitoneOn`), because $c'$ may be constant (linear cost). The domain is $v_j>0$, where all arguments of $c'$ lie in $(0,1)$.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 15 (PDF 17), proof of Theorem 5

import Mathlib
import Definitions.Def_AssortSearch_SearchQC_Model
import Definitions.Def_AssortSearch_SearchQC_ProofTerms

namespace AssortSearch.SearchQC

/-- p. 15: for a cost `c` concave on `[0, 1]` and differentiable on `(0, 1)`, `f(v_j)` is
nondecreasing and `g(v_j)` is nonincreasing in `v_j > 0`. -/
theorem f_mono_g_anti {n : ℕ} (v : Fin n → ℝ) (v0 lam m : ℝ) (c : ℝ → ℝ)
    (S : Finset (Fin n))
    (hv : ∀ i, 0 < v i) (hv0 : 0 < v0) (hlam : 0 < lam)
    (hconc : ConcaveOn ℝ (Set.Icc 0 1) c) (hdiff : DifferentiableOn ℝ c (Set.Ioo 0 1)) :
    MonotoneOn (fFn m c lam (VS v v0 S)) (Set.Ioi 0) ∧
      AntitoneOn (gFn m c lam v S (VS v v0 S)) (Set.Ioi 0) := by sorry

end AssortSearch.SearchQC
