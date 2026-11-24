-- Prove2me | Theorems.Thm_EquilibriumExperiment_Gradient_Supplement_theorem_7_counterexample
-- name    : EquilibriumExperiment.Gradient.Supplement.theorem_7_counterexample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:18:46.53589+00:00
-- url     : https://prove2.me/theorems/53b72ab9-dd75-4dba-91d7-3a6867019ed0
-- title:
--   Theorem 7 (companion theorem; not used in the proof of the goal) — (corrected: market counterexample to (4.6))
-- statement:
--   There exists a two-context market with all shared primitives and all standing assumptions of the published model, such that on $I=[1,3]$ its two utility functions are
--   $$u_0(p)=10-\frac{(p-3)^2}{4},\qquad u_1(p)=10-\frac{(p-1)^2}{4}.$$
--   Both utilities are $\sigma$-strongly concave with $\sigma=1/2$ and satisfy $|u'_a(p)|\le1<M=101/100$. Take $\eta=101/50>\sigma^{-1}$, $p_1=1$, the state path $(0,1)$, comparator $p=5/3$, horizon $T=2$ and perturbation scale $\zeta_n=n^{-1/4}$. Run exactly (4.5), using the published stochastic gradient estimator at each current payment. Then
--   $$\lim_{n\to\infty}\mathbb P\!\left[\frac12\sum_{t=1}^2 t\bigl(u_{A_t}(5/3)-u_{A_t}(p_t)\bigr)\le\frac{\eta M^2}{2}\right]=0.$$
--   The printed Theorem 7 asserts that this limit is one. This counterexample tests that claim within the source market class, rather than only the abstract exact-gradient optimization layer. The underlying common revenue and choice functions, and verification of the standing assumptions, are specified in DISPROOF.md. No improved regret theorem is claimed.
--
--   **Formalization Note** The Lean target asserts existence of the complete market, smoothness of $\omega$ and $r$ on the closed half-line $[0,\infty)$ (Definition 5 and Assumption 3 read at the boundary, stricter than the published `Standing`), its exact utility and derivative identities on $[1,3]$, strong concavity, strict gradient bound, positive activation, and the stochastic probability limit. The two states have deterministic scaled demand; their revenue function is shared. The finite context path is fixed, as permitted on p. 22. Only asymptotic market sizes matter, so the non-admissible small-$n$ perturbations do not affect the limit.
--
--   Differences from the source:
--   - correction: Theorem 7 claims probability tending to one for every admissible market → an admissible two-state market has that probability tending to zero for T=2; reason: the complete shared-primitive market construction in DISPROOF.md realizes the quadratic counterexample; no replacement regret constant is asserted.
--   - encoding: conditional period draws at the adaptive payments → independent centered raw draws with causal translation before activation and gradient estimation; reason: translation gives exactly the prescribed conditional sample law at the current payment.
--   - reading: the introductory prose mentions a gradient at p_{t-1} → the estimator uses p_t; reason: step 1 and equation (4.5) specify the current payment.
-- source:
--   Wager & Xu, Experimenting in Equilibrium, arXiv:1903.02124v5, p. 22, Theorem 7, (4.5)–(4.6); p. 39, proof, (A.10)–(A.13). Counterexample construction: local DISPROOF.md.

import Mathlib
import Definitions.Def_EquilibriumExperiment_Gradient_Supplement_Learning

open MeasureTheory ProbabilityTheory Filter Topology

namespace EquilibriumExperiment.Gradient.Supplement

/-- Counterexample to the printed Theorem 7, within the shared-primitive market class.
The two contexts have utility 10-(p-3)²/4 and 10-(p-1)²/4 on [1,3]. -/
theorem theorem_7_counterexample :
    ∃ E : ContextFamily (Fin 2) Unit,
      (∀ a, (E.market a).Standing) ∧
      (∀ a, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (E.market a).ω (Set.Ici 0) ∧
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (E.market a).r (Set.Ici 0)) ∧
      (∀ a, ∀ p ∈ Set.Icc (1 : ℝ) 3,
        0 < ∫ b, (E.market a).f b (p * (E.market a).omegaSup) ∂(E.market a).β) ∧
      (∀ a, ∀ p ∈ Set.Icc (1 : ℝ) 3,
        (E.market a).u p = 10 - (p - (if a = 0 then 3 else 1)) ^ 2 / 4 ∧
        HasDerivAt (E.market a).u (-(p - (if a = 0 then 3 else 1)) / 2) p) ∧
      (∀ a, StrongConcavityOn (E.market a).u (1 / 2) 1 3) ∧
      (∀ a, ∀ p ∈ Set.Icc (1 : ℝ) 3, |deriv (E.market a).u p| < 101 / 100) ∧
      Tendsto (fun n : ℕ =>
        seedLaw E (fun t : Fin 2 => t) n ((n : ℝ) ^ (-(1 / 4 : ℝ)))
          {x | weightedRegret E (fun t : Fin 2 => t) n
            ((n : ℝ) ^ (-(1 / 4 : ℝ))) 1 3 (101 / 50) 1 (5 / 3) x ≤
            (101 / 50 : ℝ) * (101 / 100) ^ 2 / 2}) atTop (𝓝 0) := by sorry

end EquilibriumExperiment.Gradient.Supplement
