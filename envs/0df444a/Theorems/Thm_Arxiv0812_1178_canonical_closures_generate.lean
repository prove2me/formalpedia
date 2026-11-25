-- Prove2me | Theorems.Thm_Arxiv0812_1178_canonical_closures_generate
-- name    : Arxiv0812_1178.canonical_closures_generate
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T08:46:38.696319+00:00
-- url     : https://prove2.me/theorems/b2f5adbd-008d-453d-93bb-baae1483746b
-- title:
--   Sec. 2.C, first property: the canonical closure phases generate all closure phases
-- statement:
--   Let $N_t\ge3$ and let $\phi_{kl}$ be phases on ordered pairs of telescopes that satisfy the antisymmetry $\phi_{lk}=-\phi_{kl}$. Write $\beta_{klm}=\phi_{kl}+\phi_{lm}+\phi_{mk}$. Then:
--
--   1. For all telescopes $k,l,m$,
--   $$\beta_{klm}=\beta_{1kl}+\beta_{1lm}-\beta_{1km}.$$
--   2. For pairwise distinct $k,l,m$, the closure phase $\beta_{klm}$ is a linear combination with integer coefficients of the $(N_t-1)(N_t-2)/2$ canonical closure phases $\beta_{1kl}$, $1<k<l$. The coefficients depend only on $(k,l,m)$, not on $\phi$.
--   3. The closure operator $C$ maps the vector of baseline phases $(\phi_{kl})_{k<l}$ to the vector of canonical closure phases: $C\phi=(\beta_{1kl})_{1<k<l}$.
--
--   So the canonical closures generate all three-telescope closure phases of a complete array.
--
--   **Formalization Note** The paper states the identity for the measured phases modulo $2\pi$. It is proved here as an identity of real numbers, which implies the identity modulo $2\pi$. The antisymmetry $\phi_{lk}=-\phi_{kl}$ is implicit in the paper and is a hypothesis here.
-- source:
--   Meimon, Mugnier and Le Besnerais, A self-calibration approach for optical long baseline interferometry imaging, arXiv:0812.1178v1 (2008), claim c001; Sec. 2.C, first property after eq. (10), PDF pp. 4-5; operator C of Appendix A, eq. (39), PDF p. 17

import Mathlib
import Definitions.Def_Arxiv0812_1178_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace Arxiv0812_1178

theorem canonical_closures_generate {n : ℕ} (hn : 3 ≤ n) (t1 : Fin n) (ht1 : t1.1 = 0) :
    (∀ φ : Fin n → Fin n → ℝ, (∀ k l, φ l k = -φ k l) →
      ∀ k l m : Fin n, closurePhase φ k l m =
        closurePhase φ t1 k l + closurePhase φ t1 l m - closurePhase φ t1 k m) ∧
    (∀ k l m : Fin n, k ≠ l → l ≠ m → k ≠ m →
      ∃ w : ClosureIdx n → ℤ, ∀ φ : Fin n → Fin n → ℝ, (∀ k' l', φ l' k' = -φ k' l') →
        closurePhase φ k l m = ∑ c, (w c : ℝ) * canonicalClosure φ c) ∧
    (∀ φ : Fin n → Fin n → ℝ, (∀ k l, φ l k = -φ k l) →
      closureOp n *ᵥ baselineVec φ = canonicalClosure φ) := by sorry

end Arxiv0812_1178
