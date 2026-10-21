-- Prove2me | Theorems.Thm_ExtFSMFG_Existence_proposition_3_9
-- name    : ExtFSMFG.Existence.proposition_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:01.592217+00:00
-- url     : https://prove2.me/theorems/119cf520-b418-42df-9306-6afc94f2fa7b
-- title:
--   Proposition 3.9, p. 10 — BSDE (29) is uniquely solvable, V(p, ν) = E^P[Y₀], and α̂ of (30) is the dt ⊗ dP-a.e. unique optimal control
-- statement:
--   Assume $T>0$, $A$ compact, $\mathbb P$ the reference measure, Assumptions 2.2, 2.7, 3.4 and the regularity of $f,q$. For measurable flows $p:[0,T]\to\mathcal S$ and $\nu:[0,T]\to\mathcal P(A)$, the BSDE
--   $$Y_t=g(X_T,p_T)+\int_t^T\hat H(s,X_{s-},Z_s,p_s,\nu_s)\,ds-\int_t^TZ_s^*\,d\mathcal M_s\qquad(29)$$
--   has a solution, unique in the sense of Lemma 3.1. For every solution $(Y,Z)$, with $\hat\alpha_t=\hat a(t,X_{t-},Z_t,p_t)$ (30):
--   1. $\hat\alpha\in\mathbb A$;
--   2. $\mathbb E^{\mathbb P}[Y_0]\le J(\beta,p,\nu)$ for every $\beta\in\mathbb A$, and $J(\hat\alpha,p,\nu)=\mathbb E^{\mathbb P}[Y_0]$, so $V(p,\nu)=\mathbb E^{\mathbb P}[Y_0]$ and $\hat\alpha$ is optimal;
--   3. every $\beta\in\mathbb A$ with $J(\beta,p,\nu)=\mathbb E^{\mathbb P}[Y_0]$ (an optimal control) satisfies $\beta_t=\hat\alpha_t$ for $dt\otimes d\mathbb P$-almost every $(t,\omega)\in[0,T]\times\Omega$.
--
--   This is the best-response characterization the existence proof uses to identify a fixed point of $\Phi$ as a Nash equilibrium.
--
--   **Formalization Note** The value $V(p,\nu)=\inf_{\alpha\in\mathbb A}J(\alpha,p,\nu)$ of (13) is stated through the two inequalities, without forming the infimum.
-- source:
--   Carmona & Wang, A Probabilistic Approach to Extended Finite State Mean Field Games, arXiv:1808.07635v1, p. 10, Proposition 3.9, (13), (29), (30)

import Mathlib
import Definitions.Def_ExtFSMFG_Existence_Model
import Definitions.Def_ExtFSMFG_Existence_BSDE

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ExtFSMFG.Existence

theorem proposition_3_9 {m l : ℕ} {T : ℝ≥0} (hT : 0 < T)
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
    (ν : ℝ≥0 → PA A) (hν : Measurable fun t : Set.Icc (0 : ℝ≥0) T => ν t) :
    (∃ Y Z, SolvesBSDE P (fun ω => g (Xc T ω) (p T))
        (fun ω s _ z => Hhat q f s (Xm s ω) z (p s) (ν s)) Y Z) ∧
      BSDEUnique P (fun ω => g (Xc T ω) (p T))
        (fun ω s _ z => Hhat q f s (Xm s ω) z (p s) (ν s)) ∧
      ∀ Y Z, SolvesBSDE P (fun ω => g (Xc T ω) (p T))
          (fun ω s _ z => Hhat q f s (Xm s ω) z (p s) (ν s)) Y Z →
        IsStrategy T A (ahatProc ahat Z p) ∧
        (∀ β, IsStrategy T A β → ∫ ω, Y 0 ω ∂P ≤ Jcost P q f g β p ν) ∧
        Jcost P q f g (ahatProc ahat Z p) p ν = ∫ ω, Y 0 ω ∂P ∧
        ∀ β, IsStrategy T A β → Jcost P q f g β p ν = ∫ ω, Y 0 ω ∂P →
          ∀ᵐ x ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod P),
            β x.1.toNNReal x.2 = ahatProc ahat Z p x.1.toNNReal x.2 := by sorry

end ExtFSMFG.Existence
