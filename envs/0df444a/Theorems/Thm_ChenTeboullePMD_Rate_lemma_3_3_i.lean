-- Prove2me | Theorems.Thm_ChenTeboullePMD_Rate_lemma_3_3_i
-- name    : ChenTeboullePMD.Rate.lemma_3_3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:39:55.11173+00:00
-- url     : https://prove2.me/theorems/7a26c4fc-cce2-4b81-af3e-69d614a1451a
-- title:
--   Lemma 3.3(i), p. 541 — PMD objective values are nonincreasing
-- statement:
--   Under Lemma 3.2's standing assumptions, the PMD objective values do not increase: whenever the preceding iterate belongs to the effective domain $C$,
--   $$
--   f(x^k)\le f(x^{k-1})\qquad(k\ge1).
--   $$
--
--   Monotonicity is used to identify the limiting objective value in Theorem 3.4.
--
--   **Formalization Note** The guard is needed only at the first step: $x^0$ may lie outside $C$, while every produced iterate lies in $C$. This real inequality represents the nontrivial part of the page's extended-valued monotonicity claim. The ambient space is a finite-dimensional real normed space and the run is explicit.
-- source:
--   Chen & Teboulle, Convergence analysis of a proximal-like minimization algorithm using Bregman functions, SIAM J. Optim. 3 (1993), p. 541, Lemma 3.3(i)

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting
import Definitions.Def_ChenTeboullePMD_Rate_Setting

namespace ChenTeboullePMD.Rate

/-- Lemma 3.3(i), p. 541. -/
theorem lemma_3_3_i {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (S : Set E) (ψ : E → ℝ) (hψ : IsBregmanFunction S ψ)
    (C : Set E) (hCne : C.Nonempty) (hCconv : Convex ℝ C)
    (f : E → ℝ) (hf : ConvexOn ℝ C f)
    (hlsc : LowerSemicontinuous (extendTop C f))
    (hri : intrinsicInterior ℝ C ⊆ S)
    (lam : ℕ → ℝ) (hlam : ∀ k, 1 ≤ k → 0 < lam k)
    (x : ℕ → E) (hrun : IsPMDRun S C ψ f lam x) :
    ∀ k : ℕ, x k ∈ C → f (x (k + 1)) ≤ f (x k) := by sorry

end ChenTeboullePMD.Rate
