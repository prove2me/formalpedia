-- Prove2me | Theorems.Thm_ChenTeboullePMD_Rate_lemma_3_3_ii
-- name    : ChenTeboullePMD.Rate.lemma_3_3_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:52:56.153667+00:00
-- url     : https://prove2.me/theorems/78bf3f46-4268-4b1e-b84e-e951274c8486
-- title:
--   Lemma 3.3(ii), p. 541 — distance to every minimizer is nonincreasing
-- statement:
--   Under Lemma 3.2's standing assumptions, let $u\in X_*$ be any minimizer of $f$ over its effective domain $C$. Then the Bregman distance from $u$ to each PMD iterate does not increase:
--   $$
--   D_\psi(u,x^k)\le D_\psi(u,x^{k-1})\qquad(k\ge1).
--   $$
--
--   This supplies the boundedness control used in the iterate convergence part of Theorem 3.4.
--
--   **Formalization Note** Membership in $X_*$ means $u\in C$ and $f(u)\le f(v)$ for all $v\in C$. The standing relative-interior condition implies $u\in\bar S$, so no separate zone hypothesis is imposed. The ambient space is finite dimensional with covector derivatives.
-- source:
--   Chen & Teboulle, Convergence analysis of a proximal-like minimization algorithm using Bregman functions, SIAM J. Optim. 3 (1993), p. 541, Lemma 3.3(ii)

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting
import Definitions.Def_ChenTeboullePMD_Rate_Setting

namespace ChenTeboullePMD.Rate

open BeckTeboulleMD.EMDA

/-- Lemma 3.3(ii), p. 541. -/
theorem lemma_3_3_ii {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (S : Set E) (ψ : E → ℝ) (hψ : IsBregmanFunction S ψ)
    (C : Set E) (hCne : C.Nonempty) (hCconv : Convex ℝ C)
    (f : E → ℝ) (hf : ConvexOn ℝ C f)
    (hlsc : LowerSemicontinuous (extendTop C f))
    (hri : intrinsicInterior ℝ C ⊆ S)
    (lam : ℕ → ℝ) (hlam : ∀ k, 1 ≤ k → 0 < lam k)
    (x : ℕ → E) (hrun : IsPMDRun S C ψ f lam x) :
    ∀ u, (u ∈ C ∧ ∀ v ∈ C, f u ≤ f v) →
      ∀ k : ℕ, bregman ψ u (x (k + 1)) ≤ bregman ψ u (x k) := by sorry

end ChenTeboullePMD.Rate
