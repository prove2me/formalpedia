-- Prove2me | Theorems.Thm_CvitanicKaratzas92_Optimality_lemma_A_2
-- name    : CvitanicKaratzas92.Optimality.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:23:35.28318+00:00
-- url     : https://prove2.me/theorems/835d27c6-f3aa-4315-85e0-c912b7b9ee2e
-- title:
--   Lemma A.2 — $\hat c(t)=I_1(t,(M(t)-A(t))/\hat X(t))$, $\ell\otimes P$-a.e.
-- statement:
--   Assume the standing assumptions, (5.8) for $U_2$ and every $U_1(t,\cdot)$, (8.25) and (12.2), and let $(\hat\pi,\hat c)$ with wealth $\hat X$ satisfy condition (A) for the capital $x>0$. Consider the integrable, nondecreasing process and the martingale
--   $$A(t)=\int_0^t\hat c(s)U_1'(s,\hat c(s))\,ds,\qquad M(t)=E\big[A(T)+\hat X(T)U_2'(\hat X(T))\,\big|\,\mathcal F_t\big],\qquad 0\le t\le T. \tag{A.9–A.10}$$
--   Then, $\ell\otimes P$-a.e.,
--   $$\hat c(t)=I_1\Big(t,\frac{M(t)-A(t)}{\hat X(t)}\Big). \tag{A.11}$$
--
--   This identifies the optimal consumption as the auxiliary-market optimal consumption for a candidate $\lambda$, the second step of (A) $\Rightarrow$ (B).
--
--   **Formalization Note** $M$ enters as any progressively measurable process with $M(t)=E[A(T)+\hat X(T)U_2'(\hat X(T))\mid\mathcal F_t]$ a.s. for every $t\le T$ (any two such versions agree $\ell\otimes P$-a.e.), so that the $\ell\otimes P$-a.e. statement is about a jointly measurable process.
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), p. 807, Appendix A, (A.9)–(A.10), Lemma A.2

import Mathlib
import Definitions.Def_CvitanicKaratzas92_Optimality_Conditions

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CvitanicKaratzas92.Optimality

/-- Cvitanić–Karatzas (1992), Lemma A.2, p. 807. Under (5.8), (8.25) and (12.2), let `(π̂, ĉ)`
with wealth `X̂` satisfy (A) for the capital `x > 0`, let (A.9) `A(t) = ∫₀ᵗ ĉ(s)U₁'(s, ĉ(s)) ds`
and let `M` be (a progressively measurable version of) the martingale (A.10)
`M(t) = E[A(T) + X̂(T)U₂'(X̂(T)) | 𝓕_t]`. Then, `ℓ ⊗ P`-a.e., (A.11)
`ĉ(t) = I₁(t, (M(t) − A(t))/X̂(t))`. -/
theorem lemma_A_2 {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) → ℝ≥0 → Ω → ℝ)
    (M : Market Ω d) (K : Set (EuclideanSpace ℝ (Fin d)))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (hS : Standing P 𝓕 T W I M K U1 U2)
    (h58_1 : ∀ t ≤ T, Cond58 (U1 t)) (h58_2 : Cond58 U2) (h825 : Cond825 T U1 U2)
    (h122 : Cond122 P 𝓕 T I M K U1 U2)
    (x : ℝ) (hx : 0 < x) (τ : Triple Ω d) (hA : CondA P 𝓕 T I M K U1 U2 x τ)
    (Mt : ℝ≥0 → Ω → ℝ) (hMprog : IsStronglyProgressive 𝓕 Mt)
    (hMver : ∀ t ≤ T, Mt t =ᵐ[P] condExp (𝓕 t) P (fun ω =>
      (∫ s in Icc (0 : ℝ) T, τ.c s.toNNReal ω * deriv (U1 s.toNNReal) (τ.c s.toNNReal ω)) +
        τ.X T ω * deriv U2 (τ.X T ω))) :
    ∀ᵐ q ∂(lebP P T), τ.c q.1.toNNReal q.2 =
      invMarginal (U1 q.1.toNNReal)
        ((Mt q.1.toNNReal q.2 -
            ∫ s in Icc (0 : ℝ) q.1.toNNReal,
              τ.c s.toNNReal q.2 * deriv (U1 s.toNNReal) (τ.c s.toNNReal q.2)) /
          τ.X q.1.toNNReal q.2) := by sorry


end CvitanicKaratzas92.Optimality
