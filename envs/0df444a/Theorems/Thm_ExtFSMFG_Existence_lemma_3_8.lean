-- Prove2me | Theorems.Thm_ExtFSMFG_Existence_lemma_3_8
-- name    : ExtFSMFG.Existence.lemma_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:23.359135+00:00
-- url     : https://prove2.me/theorems/17b3eae9-0863-4424-b305-5233dd284a4b
-- title:
--   Lemma 3.8, p. 10 — the BSDE (28) with driver H has a unique solution and J(α, p, ν) = E^P[Y₀]
-- statement:
--   Assume $T>0$, $A$ compact, $\mathbb P$ the reference measure, Assumptions 2.2, 2.7, 3.4 and the regularity of $f,q$. Fix measurable flows $p:[0,T]\to\mathcal S$ and $\nu:[0,T]\to\mathcal P(A)$ and a strategy $\alpha\in\mathbb A$. Then the BSDE
--   $$Y_t=g(X_T,p_T)+\int_t^TH(s,X_{s-},Z_s,\alpha_s,p_s,\nu_s)\,ds-\int_t^TZ_s^*\,d\mathcal M_s\qquad(28)$$
--   has a solution $(Y,Z)$, unique in the sense of Lemma 3.1, and for every solution
--   $$J(\alpha,p,\nu)=\mathbb E^{\mathbb P}[Y_0].$$
--
--   This represents the cost of an arbitrary strategy by a BSDE under the reference measure, the first step of the comparison argument for optimality.
-- source:
--   Carmona & Wang, A Probabilistic Approach to Extended Finite State Mean Field Games, arXiv:1808.07635v1, p. 10, Lemma 3.8, (28)

import Mathlib
import Definitions.Def_ExtFSMFG_Existence_Model
import Definitions.Def_ExtFSMFG_Existence_BSDE

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ExtFSMFG.Existence

theorem lemma_3_8 {m l : ℕ} {T : ℝ≥0} (hT : 0 < T)
    (A : Set (EuclideanSpace ℝ (Fin l))) (hA : IsCompact A)
    (p₀ : stdSimplex ℝ (Fin m)) (P : Measure (Omega m T)) [IsProbabilityMeasure P]
    (hP : IsReference T p₀ P)
    (q : ℝ≥0 → Fin m → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ)
    (f : ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ)
    (g : Fin m → (Fin m → ℝ) → ℝ)
    (ahat : ℝ≥0 → Fin m → (Fin m → ℝ) → (Fin m → ℝ) → EuclideanSpace ℝ (Fin l))
    (h22 : Assumption22 T A q) (h27 : Assumption27 T A f g) (h34 : Assumption34 T A q f ahat)
    (hreg : RegularData T A q f)
    (p : ℝ≥0 → Fin m → ℝ) (hp : Measurable fun t : Set.Icc (0 : ℝ≥0) T => p t)
    (hpS : ∀ t ≤ T, p t ∈ stdSimplex ℝ (Fin m))
    (ν : ℝ≥0 → PA A) (hν : Measurable fun t : Set.Icc (0 : ℝ≥0) T => ν t)
    (α : ℝ≥0 → Omega m T → EuclideanSpace ℝ (Fin l)) (hα : IsStrategy T A α) :
    (∃ Y Z, SolvesBSDE P (fun ω => g (Xc T ω) (p T))
        (fun ω s _ z => Hi q f s (Xm s ω) z (α s ω) (p s) (ν s)) Y Z) ∧
      BSDEUnique P (fun ω => g (Xc T ω) (p T))
        (fun ω s _ z => Hi q f s (Xm s ω) z (α s ω) (p s) (ν s)) ∧
      ∀ Y Z, SolvesBSDE P (fun ω => g (Xc T ω) (p T))
          (fun ω s _ z => Hi q f s (Xm s ω) z (α s ω) (p s) (ν s)) Y Z →
        Jcost P q f g α p ν = ∫ ω, Y 0 ω ∂P := by sorry

end ExtFSMFG.Existence
